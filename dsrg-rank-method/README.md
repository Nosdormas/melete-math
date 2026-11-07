# Machine checks: the rank of A − θI at a vertex

This directory holds the machine steps of the proofs that no directed strongly regular graph (DSRG) exists with the ten parameter sets below. Every proof bounds the rank of A − θI, where θ is an eigenvalue of the adjacency matrix A, on a few rows around one vertex. A machine step is one of three things: a theorem accepted by the Lean kernel, a run of a program whose expected output is listed in the tables below, or a SAT proof checked by drat-trim and by our own LRAT checker. The steps that the paper proves by hand are not repeated here.

## The ten parameter sets

A parameter set (v, k, t, λ, μ) names v vertices, in- and out-degree k, t two-cycles at every vertex, and λ or μ paths of length two from x to y when x → y is an arc or when it is not. The complement of a DSRG is a DSRG, so each result also excludes the complementary set; `lean/DsrgRank/Complement.lean` proves this step in Lean.

| Parameter set | Argument | Lean | Programs |
|---|---|---|---|
| (50, 11, 7, 0, 3), (68, 13, 7, 0, 3), (100, 16, 7, 0, 3), (108, 19, 9, 0, 4) | for λ = 0, the submatrix of A − θI on the closed out-neighbourhood of a vertex is nonsingular, so 2k − t ≤ m′ | `ClosedNeighbourhood.lean`: `ClosedNbhd_no_50_11_7_0_3` and three more | cross-check on known graphs and on the table: "Sets with λ = 0" |
| (48, 9, 5, 0, 2) | the Schur complement of that submatrix has rank 1; the graph is then fixed by one pivot vertex, and a finite search finds none | `SchurComplement.lean`, `VertexRecovery.lean` | "The set (48, 9, 5, 0, 2)": structure at a vertex, first and second search programs |
| (55, 16, 12, 1, 6) | for λ = 1, t = 2μ, the left kernel of A − I on a vertex and its out-neighbours; a search over profiles leaves none | `LeftKernel.lean`, `ProfileBound.lean` | "The set (55, 16, 12, 1, 6)": two programs |
| (96, 15, 10, 9, 1) | for t = λ + 1, the rows of A + I fall into classes of equal rows, and their sizes contradict the parameters | `TwinClasses.lean`, `TwinClassesMuOne.lean`: `TwinMuOne_no_96_15_10_9_1` | "Sets with μ = 1" |
| (66, 10, 5, 4, 1), (91, 12, 6, 5, 1) | for μ = 1, t = λ + 1 and k = 2λ + 2, every vertex has a row twin and a column twin once λ ≥ 3, and for λ ≥ 4 this is impossible | `TwinClassesMuOne.lean`: `TwinMuOne_no_66_10_5_4_1`, `TwinMuOne_no_91_12_6_5_1` | "Sets with μ = 1" |
| (28, 6, 3, 2, 1) | the same family with λ = 2: a vertex without a row twin is excluded by a SAT proof, the other cases in Lean | `VertexFrame.lean` | "The set (28, 6, 3, 2, 1)": two programs and a stored LRAT proof |

The Lean modules also prove the same bound for six sets with λ = 0 that the table already marks as nonexistent, and for (40, 9, 6, 5, 1) and (80, 19, 13, 12, 2). The correspondence between the statements of the paper and the Lean theorems is given in the paper.

## Layout

| Path | Contents |
|---|---|
| `checks/` | the programs and Lean files run by the commands below |
| `lib/` | shared code: exact linear algebra over the rationals, graph catalogues and their exact verification, necessary conditions on parameters, SAT calls, the LRAT checker `sat_certificate.py` |
| `data/brouwer-dsrg-v110.txt` | snapshot of the Hobart–Brouwer table of DSRG parameters with v ≤ 110, page of 6 November 2026 |
| `data/graphs/` | catalogues of known DSRGs used as positive controls, each graph with its construction |
| `data/dsrg28-control-graphs.json` | 27 known graphs of 11 parameter sets with μ = 1 and t = λ + 1, from (6, 2, 1, 0, 1) to (54, 8, 3, 2, 1), for the controls of the second program for (28, 6, 3, 2, 1); the commands below use those of (18, 5, 3, 2, 1) and (54, 8, 3, 2, 1) |
| `data/search48-second-order-*.json` | the order of pivot orbits of the second program for (48, 9, 5, 0, 2); the program rebuilds it if the file is missing |
| `data/search48-second-proofs-sha256.json` | the SHA-256 of the formula, the DRAT proof and the LRAT proof of every pivot orbit of (48, 9, 5, 0, 2), or "empty clause" for an orbit whose formula contains it |
| `data/left-kernel-check-output.txt` | output of `checks/left_kernel_check.py`, read by `checks/profiles_second.py` for comparison |
| `lean/` | Lake project `dsrg_rank` with the library `DsrgRank`; Lean v4.35.0, Mathlib v4.35.0 |
| `certificates/`, `certificates.json` | the stored LRAT proof and the SHA-256 of the proofs that are recreated by a command |

## Requirements and setup

The commands run from this directory. They need Python 3.12 with numpy; the commands that start with `"$SOLVER_PYTHON"` need an interpreter with python-sat, which provides CaDiCaL 1.9.5 and Minicard. `requirements.txt` lists the versions of our runs. The checks of DRAT proofs need drat-trim (github.com/marijnheule/drat-trim), whose path goes in `DRAT_TRIM`. Lean is installed with elan; the first command below downloads the compiled Mathlib, the second builds the modules of the project.

```sh
python -m pip install -r requirements.txt
export SOLVER_PYTHON=python
export DRAT_TRIM=/path/to/drat-trim
lake -d lean exe cache get
lake -d lean build
```

## How to read the tables

Each section below is a block of commands followed by a table with one row per command: the expected exit code, the expected last line of the output and the time of our run in seconds on one desktop computer. In an expected line, "…" stands for any text, usually a time or the middle of a long line. A command with `--mutate NAME`, and a Lean file named as a mutant, runs the same check with one step deliberately broken; it must fail, which shows that the check can fail. Every check ends with exit code 0 when it finds no violation, 1 when it finds one or catches its mutant, and 2 on an input error.

`MANIFEST.sha256` at the root of the repository lists the SHA-256 of every file, so a copy can be compared with the published one.

### Lean: axioms and statements

```bash
python -X utf8 checks/lean_axioms.py
python -X utf8 checks/lean_axioms.py --mutate extra-axiom
python -X utf8 checks/lean_axioms.py DsrgRank.Spectrum.Disc
lake -d lean env lean checks/closed_nbhd_examples.lean
python -X utf8 checks/closed_nbhd_lean_mutants.py
lake -d lean env lean checks/twin_examples.lean
python -X utf8 checks/twin_lean_mutants.py --only rows-upper-minus,rows-cond-strict,rows-no-16
python -X utf8 checks/twin_lean_mutants.py --only mu1-free-thr1,mu1-family-thr3
python -X utf8 checks/twin_lean_mutants.py --only mu1-no-45,mu1-class-minus,example-a16 --no-base
python -X utf8 checks/twin_lean_mutants.py --only example-w2-params
lake -d lean env lean checks/complement_mutant.lean
```

| Command | Exit | Last line | Time, s |
|---|---|---|---|
| `lean_axioms.py` | 0 | `{"modules": {"DsrgRank.Spectral":…13}, "nonstandard": {}}` | 21 |
| `--mutate extra-axiom` | 1 | `{"modules": {"DsrgRank.Spectral":…["mutant_false"]}}` | 22 |
| `lean_axioms.py DsrgRank.Spectrum.Disc` | 0 | `{"modules": {"DsrgRank.Spectrum.Disc": 16}, "nonstandard": {}}` | 15 |
| `closed_nbhd_examples.lean` | 0 | `'DsrgRank.ClosedNbhdExamples.ClosedN…Classical.choice, Quot.sound]` | 30 |
| `closed_nbhd_lean_mutants.py` | 0 | `unexpected outcomes: 0` | 142 |
| `twin_examples.lean` | 0 | `'DsrgRank.TwinExamples.TwinMuOne_ran…Classical.choice, Quot.sound]` | 45 |
| `twin_lean_mutants.py`, part 1 | 0 | `uncaught mutants and red bases: 0` | 73 |
| part 2 | 0 | `uncaught mutants and red bases: 0` | 94 |
| part 3 | 0 | `uncaught mutants and red bases: 0` | 118 |
| part 4 | 0 | `uncaught mutants and red bases: 0` | 66 |
| `complement_mutant.lean` | 1 | `  hno ?m.279 h2` | 26 |

`lean_axioms.py` lists the axioms of every theorem of the twelve main modules of the project and fails on any axiom other than `propext`, `Classical.choice` and `Quot.sound`; its mutant adds a theorem proved by a new axiom. Given a module name, it does the same for that module; the third command covers `disc_pos`, the positivity of the discriminant, which lies outside the main modules. The two example files apply the theorems to explicit matrices, so the hypotheses of the theorems can be met. The mutant programs copy a module, change one statement, for example a bound by one or a strict inequality, and require that Lean rejects the copy; `complement_mutant.lean` is `Complement.lean` with one parameter of the complement changed by one.

### The rank principle on known graphs

```bash
python -X utf8 checks/kernel_frame_check.py --quiet
python -X utf8 checks/kernel_frame_check.py --max-m 6 --mutate theta-swap --quiet
python -X utf8 checks/kernel_frame_check.py --max-m 6 --mutate scale --quiet
python -X utf8 checks/kernel_frame_check.py --max-m 6 --mutate rank --quiet
python -X utf8 checks/kernel_frame_check.py --max-m 6 --mutate frame-closed --quiet
python -X utf8 checks/kernel_frame_check.py --max-m 6 --mutate eigen --quiet
```

| Command | Exit | Last line | Time, s |
|---|---|---|---|
| `kernel_frame_check.py` | 0 | `all items hold` | 105 |
| `theta-swap` | 1 | `  14-6-3-2-3-b θ=-1 x=0: item 3 fails` | 23 |
| `scale` | 1 | `  14-7-4-3-4-a θ=-1: item 1 fails` | 22 |
| `rank` | 1 | `  14-7-4-3-4-a θ=-1: item 1 fails` | 22 |
| `frame-closed` | 1 | `  15-5-2-1-2-b θ=0: item 5: the frame is singular` | 27 |
| `eigen` | 1 | `  14-6-3-2-3-a θ=0 x=7: item 4: the right kernel gives no eigenvector` | 34 |

The general facts about A − θI used by every proof — its rank, the frame of its kernel at a vertex, the recovery of the rows outside a set from the rows on it, and the Schur complement — are checked exactly, in fractions, at every vertex of the 181 known graphs whose eigenvalue multiplicity is at most 12. These checks are controls: they show that the statements say what the paper says they do, and no proof depends on them. The mutants use the graphs with multiplicity at most 6.


### Sets with λ = 0: the closed neighbourhood

```bash
python -X utf8 checks/closed_nbhd_check.py
python -X utf8 checks/closed_nbhd_check.py --mutate plus-one
python -X utf8 checks/closed_nbhd_check.py --mutate det-mu
python -X utf8 checks/closed_nbhd_check.py --mutate lambda-one
```

| Command | Exit | Last line | Time, s |
|---|---|---|---|
| no mutant | 0 | `violations: 0 (graphs 0, sets 0)` | 12 |
| `plus-one` | 1 | `mutant plus-one: caught` | 14 |
| `det-mu` | 1 | `mutant det-mu: caught` | 14 |
| `lambda-one` | 1 | `mutant lambda-one: caught` | 14 |

At every vertex of every known graph with λ = 0 the program checks the structure of the closed out-neighbourhood N[x], the formula for the determinant of A − θI on N[x] against the exact integer determinant, and the bound |N[x]| ≤ rank(A − θI). On the table snapshot it lists the sets with λ = 0 that the bound 2k − t + 1 > m′ excludes, among them the four sets of the paper, and checks that none of them has a known construction. The proof for the four sets is the Lean module `ClosedNeighbourhood.lean`; this program controls it by direct computation, without Lean.

### The set (55, 16, 12, 1, 6): left kernel and profiles

```bash
python -X utf8 checks/left_kernel_check.py
python -X utf8 checks/left_kernel_check.py --mutate plus-one
python -X utf8 checks/left_kernel_check.py --mutate no-ell
python -X utf8 checks/left_kernel_check.py --mutate theta-swap
python -X utf8 checks/profiles_second.py profiles
python -X utf8 checks/profiles_second.py profiles --mutate no-sum
```

| Command | Exit | Last line | Time, s |
|---|---|---|---|
| `left_kernel_check.py` | 0 | `violations: 0 (bound 0, structure 0, sets 0)` | 103 |
| `plus-one` | 1 | `mutant plus-one: caught` | 104 |
| `no-ell` | 1 | `mutant no-ell: caught` | 101 |
| `theta-swap` | 1 | `mutant theta-swap: caught` | 100 |
| `profiles_second.py profiles` | 0 | `violations: 0` | 5 |
| `no-sum` | 1 | `  (98, 22, 12, 1, 6): first program…(17, 6, 21619, 16217, 3277, 2125)` | 5 |

`left_kernel_check.py` checks the lower bound on the dimension of the left kernel of A − I on the rows of a vertex and its out-neighbours, and the shape of the kernel vectors, on the known graphs with λ = 1 and t = 2μ. It then runs the search over profiles on every set of the snapshot with λ = 1 and t = 2μ: for (55, 16, 12, 1, 6) it finds 750 profiles and excludes all of them. `profiles_second.py` was written without reading the first program and repeats the search on the same sets; its `profiles` run compares its counts with `data/left-kernel-check-output.txt`, the output of our run of the first program.

### The set (48, 9, 5, 0, 2): structure at a vertex

```bash
python -X utf8 checks/schur_check.py
python -X utf8 checks/schur_check.py --mutate idem
python -X utf8 checks/vertex_recovery_check.py
python -X utf8 checks/vertex_recovery_check.py --mutate phi-delta
python -X utf8 checks/vertex_recovery_check.py --mutate pivot
python -X utf8 checks/vertex_recovery_check.py --mutate z-qp
```

| Command | Exit | Last line | Time, s |
|---|---|---|---|
| `schur_check.py` | 0 | `violations: 0` | 20 |
| `idem` | 1 | `violations: 258 (mutant idem)` | 21 |
| `vertex_recovery_check.py` | 0 | `violations: 0` | 22 |
| `phi-delta` | 1 | `violations: 5116 (mutant phi-delta)` | 24 |
| `pivot` | 1 | `violations: 258 (mutant pivot)` | 21 |
| `z-qp` | 1 | `violations: 1184 (mutant z-qp)` | 21 |

Both programs check, at every pair (vertex, root θ) of the known graphs with λ = 0 and a nonsingular submatrix on N[x], that the Schur complement outside N[x] has the form and the rank used by the paper, and that the rows of the outer vertices are recovered from their types and a pivot block. The mutants change one sign or one term of these formulas.

### The set (48, 9, 5, 0, 2): first search program

```bash
python -X utf8 checks/search48_first.py selftest
python -X utf8 checks/search48_first.py selftest --mutate no-exclude
python -X utf8 checks/search48_first.py inputs --kind C8
python -X utf8 checks/search48_first.py inputs --kind 2C4
python -X utf8 checks/search48_first.py plant
python -X utf8 checks/search48_first.py run --kind C8 --from 0 --to 352
python -X utf8 checks/search48_first.py run --kind 2C4 --from 0 --to 355
python -X utf8 checks/search48_first.py run --kind C8 --from 0 --to 352 --no-degrees
```

| Command | Exit | Last line | Time, s |
|---|---|---|---|
| `selftest` | 0 | `selftest: instances 300 × 2 (with…enumeration 857, discrepancies 0` | 2 |
| `selftest --mutate no-exclude` | 1 | `selftest: instances 300 × 2 (with…338 (mutant no-exclude)` | 2 |
| `inputs --kind C8` | 0 | `inputs C8: checked 28733 partners,…pairs in fractions; discrepancies 0` | 20 |
| `inputs --kind 2C4` | 0 | `inputs 2C4: checked 44921 partners,…pairs in fractions; discrepancies 0` | 38 |
| `plant` | 0 | `plant (Clebsch, θ = 1, S = 0):…0, 2) — 1, true cover found: True` | 0 |
| `run --kind C8` | 0 | `total run C8 [0, 352): live pivots 314, nodes 36012, solutions 0` | 82 |
| `run --kind 2C4` | 0 | `total run 2C4 [0, 355): live pivots 265, nodes 12620, solutions 0` | 97 |
| `run --kind C8 --no-degrees` | 0 | `total run C8 [0, 352): live pivots 314, nodes 36096, solutions 0` | 125 |

The first program fixes a vertex x and a pivot vertex outside N[x], and searches by exact cover for the remaining 33 outer vertices among the candidates whose types and pairwise conditions agree with the recovered matrix. `selftest` compares the exact-cover engine with full enumeration on random instances; `inputs` checks the candidates and their pairs in fractions; `plant` runs the same engine on the Clebsch graph, where the search must find the true cover. The two `run` commands search every pivot orbit of the two shapes C8 and 2C4 of the neighbourhood and find no solution; the third repeats the first without the degree counting.

### The set (48, 9, 5, 0, 2): second search program

```bash
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py cases
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py frame
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py selftest
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py control
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py control --mutate pivot-sign
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py control --mutate phi-delta
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py control --mutate key-strict
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py control --petersen
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py control --petersen --mutate pivot-sign
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py control --petersen --mutate phi-delta
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py control --petersen --mutate key-strict
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py search --kind C8 --part 0/6
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py search --kind C8 --part 1/6
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py search --kind C8 --part 2/6
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py search --kind C8 --part 3/6
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py search --kind C8 --part 4/6
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py search --kind C8 --part 5/6
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py search --kind 2C4 --part 0/6
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py search --kind 2C4 --part 1/6
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py search --kind 2C4 --part 2/6
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py search --kind 2C4 --part 3/6
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py search --kind 2C4 --part 4/6
"$SOLVER_PYTHON" -X utf8 checks/search48_second.py search --kind 2C4 --part 5/6
```

| Command | Exit | Last line | Time, s |
|---|---|---|---|
| `cases` | 0 | `violations: 0` | 1 |
| `frame` | 0 | `violations: 0` | 46 |
| `selftest` | 0 | `violations: 0` | 10 |
| `control` | 0 | `violations: 0` | 46 |
| `pivot-sign` | 1 | `mutant ['pivot-sign']: real graph lost for 96 frames — caught` | 44 |
| `phi-delta` | 1 | `mutant ['phi-delta']: real graph lost for 190 frames — caught` | 43 |
| `key-strict` | 1 | `mutant ['key-strict']: real graph lost for 120 frames — caught` | 64 |
| `control --petersen` | 0 | `violations: 0` | 1 |
| `--petersen`, `pivot-sign` | 1 | `mutant ['pivot-sign']: real graph lost for 20 frames — caught` | 1 |
| `--petersen`, `phi-delta` | 1 | `mutant ['phi-delta']: real graph lost for 20 frames — caught` | 1 |
| `--petersen`, `key-strict` | 1 | `mutant ['key-strict']: real graph lost for 20 frames — caught` | 1 |
| `C8 0/6` | 0 | `violations: 0` | 77 |
| `C8 1/6` | 0 | `violations: 0` | 76 |
| `C8 2/6` | 0 | `violations: 0` | 66 |
| `C8 3/6` | 0 | `violations: 0` | 73 |
| `C8 4/6` | 0 | `violations: 0` | 72 |
| `C8 5/6` | 0 | `violations: 0` | 93 |
| `2C4 0/6` | 0 | `violations: 0` | 53 |
| `2C4 1/6` | 0 | `violations: 0` | 81 |
| `2C4 2/6` | 0 | `violations: 0` | 61 |
| `2C4 3/6` | 0 | `violations: 0` | 64 |
| `2C4 4/6` | 0 | `violations: 0` | 72 |
| `2C4 5/6` | 0 | `violations: 0` | 92 |

The second program was written without reading the first and shares no code with it. It builds the frame, the types and the orbits itself and writes one SAT formula for each of the 707 pivot orbits: 352 of shape C8 and 355 of shape 2C4, in six parts each. The solver Minicard finds every formula unsatisfiable. `control` runs the same formulas on known graphs with λ = 0, where the formula must be satisfiable and its first solution must be a DSRG; each mutant loses the real graph. The catalogue graphs give Schur complements of rank 0, 2 and 3; `--petersen` adds the Petersen graph as a DSRG (10, 3, 3, 0, 1), whose Schur complement at θ = 1 has rank 1, as for (48, 9, 5, 0, 2). Its outer vertices repeat types, so the control drops the condition that types are distinct. The first program is built for the frame of (48, 9, 5, 0, 2) and has no such control. With `--solver cadical` the cardinality constraints are written as sequential counters and CaDiCaL solves the formula; `--proof-dir` and `--proof-orbits` make it write DRAT proofs and check them with drat-trim and the LRAT checker. With `--proof-orbits all` every orbit is checked: the formulas of 166 orbits contain the empty clause, because one of their cardinality constraints asks a cell for more triples than it has candidates or for a negative number of them, and the other 541 formulas are unsatisfiable with DRAT proofs that drat-trim accepts and LRAT proofs that the LRAT checker accepts. The section "Certificates" gives this command and its time.

### Sets with μ = 1: twin classes

```bash
python -X utf8 checks/twin_mu1_check.py
python -X utf8 checks/twin_mu1_check.py --mutate plus-one
python -X utf8 checks/twin_mu1_check.py --mutate rank-plus
python -X utf8 checks/twin_mu1_check.py --mutate lambda-three
python -X utf8 checks/twin_mu1_check.py --mutate free-all
python -X utf8 checks/twin_rows_check.py
python -X utf8 checks/twin_rows_check.py --mutate lam --quiet
python -X utf8 checks/twin_rows_check.py --mutate mu-one --quiet
python -X utf8 checks/twin_rows_check.py --mutate class-minus --quiet
python -X utf8 checks/twin_rows_check.py --mutate far-plus --quiet
python -X utf8 checks/twin_rows_check.py --mutate lower-plus --quiet
python -X utf8 checks/twin_rows_check.py --mutate upper-minus --quiet
python -X utf8 checks/twin_rows_check.py --mutate cond-strict --quiet
```

| Command | Exit | Last line | Time, s |
|---|---|---|---|
| `twin_mu1_check.py` | 0 | `violations: 0 (graphs 0, free vertices 0, sets 0)` | 2 |
| `plus-one` | 1 | `mutant plus-one: caught` | 1 |
| `rank-plus` | 1 | `mutant rank-plus: caught` | 2 |
| `lambda-three` | 1 | `mutant lambda-three: caught` | 2 |
| `free-all` | 1 | `mutant free-all: caught` | 2 |
| `twin_rows_check.py` | 0 | `violations: 0 (graphs 0, sets 0)` | 12 |
| `lam` | 1 | `mutant lam: caught` | 11 |
| `mu-one` | 1 | `mutant mu-one: caught` | 12 |
| `class-minus` | 1 | `mutant class-minus: caught` | 14 |
| `far-plus` | 1 | `mutant far-plus: caught` | 14 |
| `lower-plus` | 1 | `mutant lower-plus: caught` | 13 |
| `upper-minus` | 1 | `mutant upper-minus: caught` | 12 |
| `cond-strict` | 1 | `mutant cond-strict: caught` | 13 |

`twin_mu1_check.py` checks the statements on twin classes for μ = 1 and t = λ + 1, and `twin_rows_check.py` those for any μ, at every vertex of the known graphs that meet their hypotheses and on the sets of the snapshot. The proofs are the Lean modules `TwinClassesMuOne.lean` and `TwinClasses.lean`; these programs are their controls.

### The set (28, 6, 3, 2, 1)

```bash
"$SOLVER_PYTHON" -X utf8 checks/dsrg28_check.py
"$SOLVER_PYTHON" -X utf8 checks/dsrg28_check.py --mutate no-free --skip-proof
"$SOLVER_PYTHON" -X utf8 checks/dsrg28_check.py --mutate no-paths --skip-proof
"$SOLVER_PYTHON" -X utf8 checks/dsrg28_check.py --mutate no-twinned --skip-proof
"$SOLVER_PYTHON" -X utf8 checks/dsrg28_check.py --mutate block-plus --skip-proof
"$SOLVER_PYTHON" -X utf8 checks/dsrg28_certificate.py check
"$SOLVER_PYTHON" -X utf8 checks/dsrg28_certificate.py check --mutate drop-step
"$SOLVER_PYTHON" -X utf8 checks/dsrg28_second.py frames
"$SOLVER_PYTHON" -X utf8 checks/dsrg28_second.py frames --mutate drop-frame
"$SOLVER_PYTHON" -X utf8 checks/dsrg28_second.py frames --mutate canon-group
"$SOLVER_PYTHON" -X utf8 checks/dsrg28_second.py control --only 18,5,3,2,1
"$SOLVER_PYTHON" -X utf8 checks/dsrg28_second.py control --only 54,8,3,2,1 --per-graph 1
"$SOLVER_PYTHON" -X utf8 checks/dsrg28_second.py control --only 18,5,3,2,1 --mutate lam-shift
"$SOLVER_PYTHON" -X utf8 checks/dsrg28_second.py control --only 18,5,3,2,1 --mutate counter-shift
"$SOLVER_PYTHON" -X utf8 checks/dsrg28_second.py control --only 18,5,3,2,1 --mutate block-swap
"$SOLVER_PYTHON" -X utf8 checks/dsrg28_second.py control --only 18,5,3,2,1 --mutate sorted-strict
"$SOLVER_PYTHON" -X utf8 checks/dsrg28_second.py proof --drat-trim "$DRAT_TRIM"
"$SOLVER_PYTHON" -X utf8 checks/dsrg28_second.py proof --drat-trim "$DRAT_TRIM" --mutate cut-proof
python -X utf8 checks/vertex_frame_check.py
python -X utf8 checks/vertex_frame_check.py --mutate block-plus --quiet
python -X utf8 checks/vertex_frame_check.py --mutate cf-plus --quiet
python -X utf8 checks/vertex_frame_check.py --mutate lam-plus --quiet
python -X utf8 checks/vertex_frame_check.py --mutate pairs-geq --quiet
```

| Command | Exit | Last line | Time, s |
|---|---|---|---|
| `dsrg28_check.py` | 0 | `violations: 0` | 84 |
| `no-free` | 1 | `mutant no-free: caught` | 17 |
| `no-paths` | 1 | `mutant no-paths: caught` | 15 |
| `no-twinned` | 1 | `mutant no-twinned: caught` | 32 |
| `block-plus` | 1 | `mutant block-plus: caught` | 19 |
| `dsrg28_certificate.py check` | 0 | `violations: 0` | 11 |
| `drop-step` | 1 | `mutant drop-step: caught` | 13 |
| `dsrg28_second.py frames` | 0 | `violations: 0` | 6 |
| `drop-frame` | 1 | `mutant drop-frame: caught` | 5 |
| `canon-group` | 1 | `mutant canon-group: caught` | 5 |
| `control` (18) | 0 | `violations: 0; frame formulas 16,…graph unsolved within the limit 0` | 33 |
| `control` (54) | 0 | `violations: 0; frame formulas 2, of…graph unsolved within the limit 1` | 123 |
| `lam-shift` | 1 | `mutant lam-shift: caught` | 31 |
| `counter-shift` | 1 | `mutant counter-shift: caught` | 29 |
| `block-swap` | 1 | `mutant block-swap: caught` | 30 |
| `sorted-strict` | 1 | `mutant sorted-strict: caught` | 31 |
| `proof` | 0 | `certificates not accepted: 0` | 11 |
| `cut-proof` | 1 | `mutant cut-proof: caught` | 10 |
| `vertex_frame_check.py` | 0 | `violations: 0` | 2 |
| `block-plus` | 1 | `mutant block-plus: caught` | 2 |
| `cf-plus` | 1 | `mutant cf-plus: caught` | 2 |
| `lam-plus` | 1 | `mutant lam-plus: caught` | 2 |
| `pairs-geq` | 1 | `mutant pairs-geq: caught` | 2 |

`dsrg28_check.py` writes the formulas for a vertex without a row twin and for the case without such vertices, checks them on known graphs of the same family, solves them with CaDiCaL and passes the DRAT proofs to drat-trim and to our LRAT checker. `dsrg28_certificate.py check` rebuilds the formula of the first case, compares its SHA-256 with the stored one and checks the stored LRAT proof `certificates/free-28-6-3-2-1.lrat.xz` step by step; it needs neither a solver nor drat-trim. `dsrg28_second.py` is a second program for the same case, written separately and sharing no code with `dsrg28_check.py`: `frames` enumerates the 10⁶ labelled subgraphs on N⁺[x] and keeps the 55 allowed by the equation B² = 3B + J, `control` solves its formulas on graphs of (18, 5, 3, 2, 1) and (54, 8, 3, 2, 1), and `proof` solves both formulas for (28, 6, 3, 2, 1) with checked DRAT proofs. On (54, 8, 3, 2, 1) one formula without the graph is not solved within the time limit, which the last line counts; the control only needs the formulas with the graph to be satisfiable. `vertex_frame_check.py` checks the frame of a vertex for μ = 1 and t = λ + 1, the statement of the Lean module `VertexFrame.lean`, on known graphs, and counts the subgraphs on N⁺[x] for (28, 6, 3, 2, 1).

## What the checks do not cover

The paper marks every step of its proofs as proved in Lean, by a program or by hand. The steps proved by hand — for example the determinant formula on N[x], the passage from the Lean statements on (48, 9, 5, 0, 2) to the form used in the text, and the count c = 8 for (55, 16, 12, 1, 6) — have no machine check here. The search for (48, 9, 5, 0, 2) rests on two programs of different design without common code that agree. Both encode the reduction of the paper's Proposition 5.4, which is proved by hand, so each guards the other's implementation but not the reduction; only the second program has a control at Schur complement rank 1, on the Petersen graph. The unsatisfiability of the second program's formulas is checked for all 707 orbits, by an accepted proof or by the empty clause in the formula, but that these formulas encode the conditions of Proposition 5.4 is not proved: the construction of the formula and the controls support it. The table snapshot is an input: it records the parameter sets and statuses of the published page of 6 November 2026, and the checks do not compare these statuses with the papers behind them.

## Certificates

`certificates.json` lists every proof certificate. The LRAT proof for the vertex without a row twin in (28, 6, 3, 2, 1) is stored in `certificates/` (525 steps, compressed with xz) and is checked by `dsrg28_certificate.py check` above; `dsrg28_certificate.py make DIR` writes it again. The formulas, DRAT proofs and LRAT proofs of the second program for (48, 9, 5, 0, 2) are too large to store. The command `"$SOLVER_PYTHON" -X utf8 checks/search48_second.py search --kind KIND --solver cadical --part I/12 --proof-dir DIR --proof-orbits all --discard-proofs --drat-timeout 900`, run for KIND = C8 and 2C4 and for I = 0, …, 11, writes them again and checks them. For every orbit whose formula has no empty clause, CaDiCaL writes a DRAT proof, drat-trim checks it and writes an LRAT proof, and the LRAT checker checks that; the line of the orbit gives the SHA-256 of the three files, and the run ends with `violations: 0` only if every orbit is UNSAT and every proof is accepted. `data/search48-second-proofs-sha256.json` lists these SHA-256 for the 541 orbits with proofs and marks the other 166 as "empty clause". In our run the 24 parts took 18 895 s on one thread in total, 12 065 s for C8 and 6830 s for 2C4; one orbit took at most 285 s, the solver at most 114 s and drat-trim at most 92 s. `--discard-proofs` removes the files of each orbit after its check, so the disk holds the files of one orbit at a time; without it they stay in DIR. CaDiCaL writes the same files on a repeated run: nine orbits proved in an earlier, separate run have the same SHA-256.

## License and citation

The code is under the MIT license (`LICENSE` at the root of the repository); the data and the texts are under CC BY 4.0 (`LICENSE-DATA`). The snapshot of the Hobart–Brouwer table reproduces parameter sets and statuses from the public page of that table. To cite these files, use `CITATION.cff`.
