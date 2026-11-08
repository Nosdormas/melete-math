/-
This file is the module LRATCatcher.Basic of lrat-catcher v0.2.1 by Stefan Szeider
(https://github.com/leansolving/lrat-catcher, commit f525f242bc31c08b67d70f58c098bfd7aacda1b6).
Changes from v0.2.1: the port to Lean 4.35, marked "Port to Lean 4.35"; the module name, here
DsrgRank.Sat.LRATCatcher.Basic (the namespace LRATCatcher is kept); and this header.
The file is distributed under the MIT License of lrat-catcher:

MIT License

Copyright (c) 2026 Stefan Szeider

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Std.Sat.CNF

/-!
  # LRATCatcher.Basic — DIMACS parsing into `Std.Sat.CNF Nat`

  The parser is deliberately small and auditable: it is part of the *statement*
  of every imported theorem (the theorem speaks about `parseDimacs (include_str …)`),
  so it belongs to the trusted base alongside the Lean kernel and compiler.

  Exact parsing rule (keep this in sync with the code below):
  * only lines whose first non-whitespace character is a digit or `-` are parsed;
    every other line (comments `c …`, the header `p cnf …`, and any nonstandard
    lines such as XOR `x …` extensions) is ignored;
  * within a parsed line, tokens are read as integers; `0` terminates the current
    clause (clauses may span lines; several clauses may share a line);
  * non-integer tokens are ignored; a missing final `0` is tolerated.

  This leniency can never make a theorem unsound — the statement is about
  whatever was parsed — but it can make it differ from the file the user thinks
  they fed the solver. The elaboration commands therefore run `validateDimacs`
  (see `LRATCatcher.Reflect`), which rejects files where the leniency would matter.

  Literal convention: DIMACS literal `l ≠ 0` ↦ variable `|l| - 1` (0-indexed),
  polarity `true` iff `l > 0`. This is inverse to `Std.Sat.CNF.dimacs`' `+1` shift.
-/

@[expose] public section

open Std.Sat

namespace LRATCatcher

/-- DIMACS literal → Std literal: variable `|l| - 1` (0-indexed), polarity `l > 0`.
    Precondition `l ≠ 0` (callers treat `0` as a clause terminator first;
    on `0` this would return `(0, false)` by `Nat` truncating subtraction). -/
def dimacsLit (l : Int) : Nat × Bool := (l.natAbs - 1, decide (0 < l))

/-- Port to Lean 4.35: DIMACS literal of an LRAT step → Std literal, by
    the same rule as `dimacsLit`; `0` gives `none` and is dropped, as by the
    core checker (`Std.Tactic.BVDecide.LRAT.Internal.check.convertClause`).
    Constructor matching keeps it kernel-reducible (`LRATCatcher.Kernel`). -/
def intLit? : Int → Option (Literal Nat)
  | .ofNat 0 => none
  | .ofNat (n + 1) => some (n, true)
  | .negSucc n => some (n, false)

/-- Port to Lean 4.35: an LRAT clause (`Array Int`) as a `CNF.Clause Nat`. -/
def lratClause (c : Array Int) : CNF.Clause Nat :=
  CNF.Clause.ofLiterals (c.toList.filterMap intLit?)

/-- Parse a DIMACS CNF string; see the module docstring for the exact rule. -/
def parseDimacs (s : String) : CNF Nat := Id.run do
  let mut clauses : Array (CNF.Clause Nat) := #[]
  -- Port to Lean 4.35: a clause is now a packed structure, so the
  -- literals of the current clause are collected in a list (in reverse) and
  -- packed with `CNF.Clause.ofLiterals`, whose `literals` are exactly that
  -- list (`CNF.Clause.literals_ofLiterals`).
  let mut cur : List (Literal Nat) := []
  for line in s.splitOn "\n" do
    let t := line.trimAscii.toString
    if t.isEmpty then
      continue
    -- only clause lines: first character a digit or '-'
    unless t.front.isDigit || t.front == '-' do
      continue
    for tok in t.split (fun ch => ch == ' ' || ch == '\t') do
      match tok.toInt? with
      | some 0 =>
        clauses := clauses.push (CNF.Clause.ofLiterals cur.reverse)
        cur := []
      | some l => cur := dimacsLit l :: cur
      | none => pure ()
  -- tolerate a missing final 0
  if !cur.isEmpty then
    clauses := clauses.push (CNF.Clause.ofLiterals cur.reverse)
  return { clauses }

/-- Runtime round-trip self-check: printing with `Std.Sat.CNF.dimacs` and
    re-parsing reproduces the clauses exactly. Used by the exporter and
    generator executables on every file they write — a cheap substitute for
    a verified printer/parser round-trip theorem (descoped: string proofs
    are costly). -/
def dimacsRoundTrip (cnf : CNF Nat) : Bool :=
  (parseDimacs cnf.dimacs).clauses == cnf.clauses

end LRATCatcher
