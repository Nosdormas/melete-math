from __future__ import annotations

import sys
import time
from contextlib import contextmanager
from pathlib import Path


def release(s) -> None:
    inner = getattr(s, "solver", None)
    if inner is not None and getattr(inner, "cadical", None) and getattr(inner, "prfp", None) is not None:
        import pysolvers
        prfp, prfile = inner.prfp, inner.prfile
        pysolvers.cadical195_del(inner.cadical, prfile)
        inner.cadical = None
        pysolvers.flushpr(prfp)
        prfile.close()
        inner.prfile = inner.prfp = None
    s.delete()


@contextmanager
def proof_solver(name: str = "cadical195", **kwargs):
    from pysat.solvers import Solver
    s = Solver(name=name, **kwargs)
    try:
        yield s
    finally:
        release(s)


CERT = str(Path(__file__).resolve().parent.parent / "lib")


def _deadline_child(conn, clauses, name, assumptions, want_model, proof):
    rec = {}
    with proof_solver(name, bootstrap_with=clauses, with_proof=proof is not None) as s:
        r = s.solve(assumptions=assumptions)
        rec["result"] = "SAT" if r else "UNSAT"
        if r and want_model:
            rec["model"] = s.get_model()
        if not r and proof is not None:
            import pysolvers
            if CERT not in sys.path:
                sys.path.insert(0, CERT)
            import sat_certificate
            pysolvers.flushpr(s.solver.prfp)
            fh = s.solver.prfile
            fh.seek(0)
            rec["drat_sha256"] = sat_certificate.write_drat_from_binary(proof, fh)
    conn.send(rec)
    conn.close()


def _kill_on_close_job(pid):
    if sys.platform != "win32":
        return None
    import ctypes
    from ctypes import wintypes

    class Basic(ctypes.Structure):
        _fields_ = [("PerProcessUserTimeLimit", ctypes.c_int64), ("PerJobUserTimeLimit", ctypes.c_int64),
                    ("LimitFlags", wintypes.DWORD), ("MinimumWorkingSetSize", ctypes.c_size_t),
                    ("MaximumWorkingSetSize", ctypes.c_size_t), ("ActiveProcessLimit", wintypes.DWORD),
                    ("Affinity", ctypes.c_size_t), ("PriorityClass", wintypes.DWORD),
                    ("SchedulingClass", wintypes.DWORD)]

    class Io(ctypes.Structure):
        _fields_ = [(f, ctypes.c_uint64) for f in ("ReadOperationCount", "WriteOperationCount",
                                                   "OtherOperationCount", "ReadTransferCount",
                                                   "WriteTransferCount", "OtherTransferCount")]

    class Extended(ctypes.Structure):
        _fields_ = [("BasicLimitInformation", Basic), ("IoInfo", Io),
                    ("ProcessMemoryLimit", ctypes.c_size_t), ("JobMemoryLimit", ctypes.c_size_t),
                    ("PeakProcessMemoryUsed", ctypes.c_size_t), ("PeakJobMemoryUsed", ctypes.c_size_t)]

    k32 = ctypes.WinDLL("kernel32", use_last_error=True)
    k32.CreateJobObjectW.restype = wintypes.HANDLE
    k32.CreateJobObjectW.argtypes = [ctypes.c_void_p, wintypes.LPCWSTR]
    k32.SetInformationJobObject.argtypes = [wintypes.HANDLE, ctypes.c_int, ctypes.c_void_p, wintypes.DWORD]
    k32.OpenProcess.restype = wintypes.HANDLE
    k32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    k32.AssignProcessToJobObject.argtypes = [wintypes.HANDLE, wintypes.HANDLE]
    k32.CloseHandle.argtypes = [wintypes.HANDLE]
    job = k32.CreateJobObjectW(None, None)
    if not job:
        return None
    info = Extended()
    info.BasicLimitInformation.LimitFlags = 0x2000  # JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE
    ok = k32.SetInformationJobObject(job, 9, ctypes.byref(info), ctypes.sizeof(info))  # 9 — Extended
    proc = k32.OpenProcess(0x0101, False, pid) if ok else None  # PROCESS_SET_QUOTA | PROCESS_TERMINATE
    ok = bool(proc) and k32.AssignProcessToJobObject(job, proc)
    if proc:
        k32.CloseHandle(proc)
    if not ok:
        k32.CloseHandle(job)
        return None
    return job


def _close_job(job) -> None:
    if job is not None:
        import ctypes
        from ctypes import wintypes
        k32 = ctypes.WinDLL("kernel32")
        k32.CloseHandle.argtypes = [wintypes.HANDLE]
        k32.CloseHandle(job)


def solve_with_deadline(clauses, seconds: float, *, name: str = "cadical195", assumptions=(),
                        model: bool = False, proof=None, grace: float = 5.0) -> dict:
    import multiprocessing as mp
    from multiprocessing.connection import wait
    ctx = mp.get_context("spawn")
    recv, send = ctx.Pipe(duplex=False)
    p = ctx.Process(target=_deadline_child, args=(send, list(clauses), name, list(assumptions), model,
                                                  None if proof is None else str(proof)), daemon=True)
    t0 = time.monotonic()
    p.start()
    send.close()
    job = _kill_on_close_job(p.pid)
    rec = {"result": "TIMEOUT", "pid": p.pid}
    try:
        ready = wait([recv, p.sentinel], timeout=max(0.0, t0 + seconds - time.monotonic()))
        if ready:
            try:
                got = recv in ready or recv.poll(0)
                if got:
                    rec.update(recv.recv())
            except (EOFError, OSError):
                got = False
            if not got:
                rec["result"] = "CRASH"
        rec["elapsed_s"] = round(time.monotonic() - t0, 2)
        if rec["result"] in ("SAT", "UNSAT"):
            p.join(grace)
    finally:
        if p.is_alive():
            p.kill()
        p.join()
        recv.close()
        _close_job(job)
    rec["exitcode"] = p.exitcode
    return rec
