/-
This file is the module LRATCatcher.Kernel of lrat-catcher v0.2.1 by Stefan Szeider
(https://github.com/leansolving/lrat-catcher, commit f525f242bc31c08b67d70f58c098bfd7aacda1b6).
Changes from v0.2.1: the port to Lean 4.35, marked "Port to Lean 4.35"; the module name, here
DsrgRank.Sat.LRATCatcher.Kernel (the namespace LRATCatcher is kept); one phrase of the module
documentation; and this header.
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

public import DsrgRank.Sat.LRATCatcher.Basic
import all Std.Sat.CNF.Sat
public import Std.Tactic.BVDecide.LRAT

/-!
  # LRATCatcher.Kernel — kernel-mode LRAT checking (zero compiler trust)

  A variant of the LRAT check whose Boolean evaluation reduces inside the
  Lean *kernel* (`decide +kernel`), so the compiled evaluator
  is not part of the trust base.

  **Port to Lean 4.35.** Up to Lean 4.30 this module cloned the
  verified core checker (`DefaultFormula`, `lratChecker`, `lratCheckerSound`)
  with kernel-reducible replacements. Lean 4.35 replaced that checker by a
  new one (`Std.Tactic.BVDecide.LRAT.Internal.State`) whose unit propagation
  runs on `Std.HashMap`/`Std.HashSet` (USize hashing does not reduce in the
  kernel) and whose loops are well-founded recursions. There is nothing left
  to clone, so this module now carries its own small checker:

  * the clause database is a `List (id × literal list)` keyed by the LRAT
    clause id (ids may have gaps, as in `drat-trim -L` output);
  * a RUP step propagates the hint clauses over an association-list partial
    assignment (`propagate`);
  * a RAT step checks, for every clause holding the negated pivot, the RUP of
    the resolvent with the step's RUP hints followed by the candidate's hints
    (`ratOK`);
  * everything is structural recursion on lists, so `decide +kernel` reduces it.

  Soundness (`checkKernel_sound`) is proved below from the semantics of
  `Std.Sat.CNF` directly; the statement is the one of v0.2.1:
  `checkKernel cnf proof = true → cnf.Unsat`.

  Statements are about a Lean-defined `CNF Nat` term (the `lrat_reflect_cnf`
  form); `parseDimacs` itself does not kernel-reduce (byte-string slice
  iteration), so there is no kernel analogue of the parsed-file statement.
-/

@[expose] public section

open Std.Sat Std.Tactic.BVDecide.LRAT

namespace LRATCatcher

/-! ## Plain-list clauses and their semantics -/

/-- A clause as a plain literal list (variable 0-indexed, as in `CNF Nat`). -/
abbrev KClause := List (Literal Nat)

/-- The kernel checker's clause database: `(LRAT clause id, clause)`,
    newest first. -/
abbrev KState := List (Nat × KClause)

/-- A clause list is satisfied by `a` (same predicate as `CNF.Clause.eval`
    on the literal list). -/
def clauseTrue (a : Nat → Bool) (c : KClause) : Bool := c.any fun (i, n) => a i == n

/-- `a` satisfies every clause of the database. -/
def StateSat (a : Nat → Bool) (st : KState) : Prop := ∀ p ∈ st, clauseTrue a p.2 = true

theorem clauseTrue_iff {a : Nat → Bool} {c : KClause} :
    clauseTrue a c = true ↔ ∃ l ∈ c, a l.1 = l.2 := by
  simp [clauseTrue]

theorem clauseTrue_eq_false_iff {a : Nat → Bool} {c : KClause} :
    clauseTrue a c = false ↔ ∀ l ∈ c, a l.1 ≠ l.2 := by
  simp [clauseTrue]

/-- The clause stored under `id` (first match). -/
def findClause : KState → Nat → Option KClause
  | [], _ => none
  | (j, c) :: rest, id => if j = id then some c else findClause rest id

theorem mem_of_findClause : ∀ {st : KState} {id : Nat} {c : KClause},
    findClause st id = some c → ∃ j, (j, c) ∈ st
  | [], _, _, h => by simp [findClause] at h
  | (j, d) :: rest, id, c, h => by
    simp only [findClause] at h
    split at h
    · cases h; exact ⟨j, List.mem_cons_self ..⟩
    · obtain ⟨j', hj'⟩ := mem_of_findClause h
      exact ⟨j', List.mem_cons_of_mem _ hj'⟩

/-! ## Partial assignments -/

/-- A partial assignment as an association list; the first entry wins. -/
def lookupVal : List (Nat × Bool) → Nat → Option Bool
  | [], _ => none
  | (w, b) :: rest, v => if w = v then some b else lookupVal rest v

theorem mem_of_lookupVal : ∀ {α : List (Nat × Bool)} {v : Nat} {b : Bool},
    lookupVal α v = some b → (v, b) ∈ α
  | [], _, _, h => by simp [lookupVal] at h
  | (w, b') :: rest, v, b, h => by
    simp only [lookupVal] at h
    split at h
    · next hw => cases h; subst hw; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_of_lookupVal h)

/-- A total assignment agrees with a partial one. -/
def Agrees (a : Nat → Bool) (α : List (Nat × Bool)) : Prop :=
  ∀ v b, lookupVal α v = some b → a v = b

theorem agrees_cons {a : Nat → Bool} {α : List (Nat × Bool)} {v : Nat} {b : Bool}
    (h : Agrees a α) (hv : a v = b) : Agrees a ((v, b) :: α) := by
  intro w c hw
  simp only [lookupVal] at hw
  split at hw
  · next hvw => cases hw; subst hvw; exact hv
  · exact h w c hw

/-- Value of a literal under a partial assignment (`none` = unassigned). -/
def litVal (α : List (Nat × Bool)) (l : Literal Nat) : Option Bool :=
  (lookupVal α l.1).map (· == l.2)

theorem litTrue_eq_false_of_litVal {a : Nat → Bool} {α : List (Nat × Bool)} {l : Literal Nat}
    (hag : Agrees a α) (h : litVal α l = some false) : a l.1 ≠ l.2 := by
  simp only [litVal, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, hxl⟩ := h
  rw [hag _ _ hx]
  intro heq
  subst heq
  simp at hxl

/-! ## Unit propagation over hint clauses -/

/-- Outcome of propagating one hint clause. -/
inductive HintRes where
  | conflict
  | unit (l : Literal Nat)
  | skip
  | fail

/-- Propagate one hint clause: a satisfied clause is skipped, a falsified one
    is a conflict, a clause whose only unassigned literal is `l` (possibly
    repeated) is unit, anything else fails. Skipping a satisfied hint can only
    make a check succeed where a stricter checker errs; it is sound because
    the assignment is left unchanged. -/
def hintStep (α : List (Nat × Bool)) (d : KClause) : HintRes :=
  if d.any (fun l => litVal α l == some true) then .skip
  else
    match d.filter (fun l => litVal α l == none) with
    | [] => .conflict
    | l :: rest => if rest.all (· == l) then .unit l else .fail

private theorem litVal_false_of_not_true_not_none {α : List (Nat × Bool)} {l : Literal Nat}
    (h1 : ¬ (litVal α l == some true) = true) (h2 : ¬ (litVal α l == none) = true) :
    litVal α l = some false := by
  cases hv : litVal α l with
  | none => simp [hv] at h2
  | some b => cases b <;> simp_all

theorem hintStep_conflict {α : List (Nat × Bool)} {d : KClause}
    (h : hintStep α d = .conflict) : ∀ l ∈ d, litVal α l = some false := by
  unfold hintStep at h
  split at h
  · cases h
  · next hany =>
    split at h
    · next hfil =>
      intro l hl
      apply litVal_false_of_not_true_not_none
      · intro ht; exact hany (List.any_eq_true.mpr ⟨l, hl, ht⟩)
      · intro hn
        have : l ∈ d.filter (fun l => litVal α l == none) := List.mem_filter.mpr ⟨hl, hn⟩
        rw [hfil] at this
        cases this
    · split at h <;> cases h

theorem hintStep_unit {α : List (Nat × Bool)} {d : KClause} {u : Literal Nat}
    (h : hintStep α d = .unit u) : ∀ l ∈ d, l ≠ u → litVal α l = some false := by
  unfold hintStep at h
  split at h
  · cases h
  · next hany =>
    split at h
    · cases h
    · next l rest hfil =>
      split at h
      · next hall =>
        cases h
        intro l' hl' hne
        apply litVal_false_of_not_true_not_none
        · intro ht; exact hany (List.any_eq_true.mpr ⟨l', hl', ht⟩)
        · intro hn
          have hmem : l' ∈ d.filter (fun l => litVal α l == none) :=
            List.mem_filter.mpr ⟨hl', hn⟩
          rw [hfil] at hmem
          rcases List.mem_cons.mp hmem with heq | hrest
          · exact hne heq
          · exact hne (by simpa using List.all_eq_true.mp hall l' hrest)
      · cases h

/-- Propagate the hint clauses `hs` (LRAT ids) starting from `α`; `true` iff
    a conflict is reached. -/
def propagate (st : KState) : List (Nat × Bool) → List Nat → Bool
  | _, [] => false
  | α, h :: hs =>
    match findClause st h with
    | none => false
    | some d =>
      match hintStep α d with
      | .conflict => true
      | .unit l => propagate st ((l.1, l.2) :: α) hs
      | .skip => propagate st α hs
      | .fail => false

theorem propagate_sound {st : KState} {a : Nat → Bool} (hst : StateSat a st) :
    ∀ {α : List (Nat × Bool)} {hs : List Nat}, propagate st α hs = true → Agrees a α → False
  | _, [], h, _ => by simp [propagate] at h
  | α, h :: hs, hp, hag => by
    simp only [propagate] at hp
    split at hp
    · cases hp
    · next d hd =>
      obtain ⟨j, hj⟩ := mem_of_findClause hd
      have hsat := hst _ hj
      simp only at hsat
      split at hp
      · next hc =>
        have hall := hintStep_conflict hc
        obtain ⟨l, hl, hal⟩ := clauseTrue_iff.mp hsat
        exact litTrue_eq_false_of_litVal hag (hall l hl) hal
      · next u hu =>
        apply propagate_sound hst hp
        apply agrees_cons hag
        obtain ⟨l, hl, hal⟩ := clauseTrue_iff.mp hsat
        by_cases hlu : l = u
        · subst hlu; exact hal
        · exact absurd hal (litTrue_eq_false_of_litVal hag (hintStep_unit hu l hl hlu))
      · exact propagate_sound hst hp hag
      · cases hp

/-! ## RUP and RAT steps -/

/-- The negation of a clause as a partial assignment. -/
def negLits (c : KClause) : List (Nat × Bool) := c.map fun l => (l.1, !l.2)

/-- A clause holding a literal and its negation. -/
def isTaut (c : KClause) : Bool := c.any fun l => c.contains (l.1, !l.2)

/-- RUP check of `c` against the database with hints `hints`. -/
def rupOK (st : KState) (c : KClause) (hints : List Nat) : Bool :=
  isTaut c || propagate st (negLits c) hints

theorem clauseTrue_of_isTaut {a : Nat → Bool} {c : KClause} (h : isTaut c = true) :
    clauseTrue a c = true := by
  simp only [isTaut, List.any_eq_true, List.contains_iff_mem] at h
  obtain ⟨l, hl, hneg⟩ := h
  apply clauseTrue_iff.mpr
  cases hal : a l.1 == l.2
  · refine ⟨(l.1, !l.2), hneg, ?_⟩
    cases hb : l.2 <;> cases ha : a l.1 <;> simp_all
  · exact ⟨l, hl, by simpa using hal⟩

theorem agrees_negLits {a : Nat → Bool} {c : KClause} (h : clauseTrue a c = false) :
    Agrees a (negLits c) := by
  intro v b hv
  have hmem := mem_of_lookupVal hv
  simp only [negLits, List.mem_map] at hmem
  obtain ⟨l, hl, hlv⟩ := hmem
  have hne := clauseTrue_eq_false_iff.mp h l hl
  simp only [Prod.mk.injEq] at hlv
  obtain ⟨rfl, rfl⟩ := hlv
  cases hb : l.2 <;> cases ha : a l.1 <;> simp_all

theorem rupOK_sound {st : KState} {c : KClause} {hints : List Nat} {a : Nat → Bool}
    (h : rupOK st c hints = true) (hst : StateSat a st) : clauseTrue a c = true := by
  simp only [rupOK, Bool.or_eq_true] at h
  rcases h with ht | hp
  · exact clauseTrue_of_isTaut ht
  · cases hc : clauseTrue a c
    · exact (propagate_sound hst hp (agrees_negLits hc)).elim
    · rfl

/-- The negation of a literal. -/
def negLit (l : Literal Nat) : Literal Nat := (l.1, !l.2)

/-- The hints of RAT candidate `id` (first match). -/
def findHints : List (Nat × List Nat) → Nat → Option (List Nat)
  | [], _ => none
  | (j, hs) :: rest, id => if j = id then some hs else findHints rest id

/-- Every clause of `sub` that holds the negated pivot has a hint group, and
    the resolvent `c ∪ (d \ {¬p})` is RUP against `st` with the step's RUP
    hints followed by the candidate's hints. -/
def ratCandidatesOK (st : KState) (c : KClause) (p : Literal Nat) (rupHints : List Nat)
    (ratHints : List (Nat × List Nat)) : KState → Bool
  | [] => true
  | (j, d) :: rest =>
    (if d.contains (negLit p) then
      match findHints ratHints j with
      | none => false
      | some hs => rupOK st (c ++ d.filter (· != negLit p)) (rupHints ++ hs)
     else true) && ratCandidatesOK st c p rupHints ratHints rest

/-- RAT check of `c` on pivot `p`. -/
def ratOK (st : KState) (c : KClause) (p : Literal Nat) (rupHints : List Nat)
    (ratHints : List (Nat × List Nat)) : Bool :=
  c.contains p && ratCandidatesOK st c p rupHints ratHints st

theorem ratCandidatesOK_sound {st : KState} {c : KClause} {p : Literal Nat}
    {rupHints : List Nat} {ratHints : List (Nat × List Nat)} {a : Nat → Bool}
    (hst : StateSat a st) :
    ∀ {sub : KState}, ratCandidatesOK st c p rupHints ratHints sub = true →
      ∀ e ∈ sub, negLit p ∈ e.2 → clauseTrue a (c ++ e.2.filter (· != negLit p)) = true
  | [], _, e, he, _ => by cases he
  | (j, d) :: rest, h, e, he, hneg => by
    simp only [ratCandidatesOK, Bool.and_eq_true] at h
    obtain ⟨hhd, htl⟩ := h
    rcases List.mem_cons.mp he with rfl | hrest
    · simp only [List.contains_iff_mem, hneg, ite_true] at hhd
      split at hhd
      · cases hhd
      · exact rupOK_sound hhd hst
    · exact ratCandidatesOK_sound hst htl e hrest hneg

/-- The RAT property: a model of the database extends, by flipping the pivot
    if needed, to a model of the database plus the new clause. -/
theorem ratOK_sound {st : KState} {c : KClause} {p : Literal Nat} {rupHints : List Nat}
    {ratHints : List (Nat × List Nat)} {a : Nat → Bool} (id : Nat)
    (h : ratOK st c p rupHints ratHints = true) (hst : StateSat a st) :
    ∃ a', StateSat a' ((id, c) :: st) := by
  simp only [ratOK, Bool.and_eq_true, List.contains_iff_mem] at h
  obtain ⟨hp, hcand⟩ := h
  cases hca : clauseTrue a c
  · -- flip the pivot
    refine ⟨fun v => if v = p.1 then p.2 else a v, ?_⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | hrest
    · exact clauseTrue_iff.mpr ⟨p, hp, by simp⟩
    · obtain ⟨j, d⟩ := e
      by_cases hneg : negLit p ∈ d
      · by_cases hpd : p ∈ d
        · exact clauseTrue_iff.mpr ⟨p, hpd, by simp⟩
        · have hres := ratCandidatesOK_sound hst hcand (j, d) hrest hneg
          obtain ⟨l, hl, hal⟩ := clauseTrue_iff.mp hres
          rcases List.mem_append.mp hl with hlc | hld
          · exact absurd hal (clauseTrue_eq_false_iff.mp hca l hlc)
          · obtain ⟨hld, hlne⟩ := List.mem_filter.mp hld
            have hvar : l.1 ≠ p.1 := by
              intro hv
              obtain ⟨v, b⟩ := l
              obtain ⟨pv, pb⟩ := p
              simp only at hv
              subst hv
              cases hb : b <;> cases hpb : pb <;> simp_all [negLit]
            exact clauseTrue_iff.mpr ⟨l, hld, by simp [hvar, hal]⟩
      · obtain ⟨l, hl, hal⟩ := clauseTrue_iff.mp (hst _ hrest)
        by_cases hvar : l.1 = p.1
        · have hlp : l = p := by
            obtain ⟨v, b⟩ := l
            obtain ⟨pv, pb⟩ := p
            simp only at hvar
            subst hvar
            cases hb : b <;> cases hpb : pb <;> simp_all [negLit]
          subst hlp
          exact clauseTrue_iff.mpr ⟨l, hl, by simp⟩
        · exact clauseTrue_iff.mpr ⟨l, hl, by simp [hvar, hal]⟩
  · refine ⟨a, ?_⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | hrest
    · exact hca
    · exact hst e hrest

/-! ## The kernel-mode check and its soundness -/

/-- An LRAT clause (`Array Int`) as a kernel clause (`intLit?` per literal). -/
def toKClause (c : Array Int) : KClause := c.toList.filterMap intLit?

/-- Run the proof against the database; `true` iff the empty clause is
    derived. Deletion drops every entry with a listed id. -/
def checkStepsK : KState → List IntAction → Bool
  | _, [] => false
  | st, .addEmpty _ hints :: _ => rupOK st [] hints.toList
  | st, .addRup id c hints :: rest =>
    let c := toKClause c
    rupOK st c hints.toList && checkStepsK ((id, c) :: st) rest
  | st, .addRat id c p rupHints ratHints :: rest =>
    let c := toKClause c
    ratOK st c (p.1 - 1, p.2) rupHints.toList (ratHints.toList.map fun x => (x.1, x.2.toList))
      && checkStepsK ((id, c) :: st) rest
  | st, .del ids :: rest =>
    let ids := ids.toList
    checkStepsK (st.filter fun e => !ids.contains e.1) rest

theorem checkStepsK_sound :
    ∀ {st : KState} {proof : List IntAction}, checkStepsK st proof = true →
      ∀ a, ¬ StateSat a st
  | _, [], h, _, _ => by simp [checkStepsK] at h
  | st, .addEmpty _ hints :: _, h, a, hst => by
    simp only [checkStepsK] at h
    have := rupOK_sound h hst
    simp [clauseTrue] at this
  | st, .addRup id c hints :: rest, h, a, hst => by
    simp only [checkStepsK, Bool.and_eq_true] at h
    obtain ⟨hrup, hrest⟩ := h
    apply checkStepsK_sound hrest a
    intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · exact rupOK_sound hrup hst
    · exact hst e he'
  | st, .addRat id c p rupHints ratHints :: rest, h, a, hst => by
    simp only [checkStepsK, Bool.and_eq_true] at h
    obtain ⟨hrat, hrest⟩ := h
    obtain ⟨a', ha'⟩ := ratOK_sound id hrat hst
    exact checkStepsK_sound hrest a' ha'
  | st, .del ids :: rest, h, a, hst => by
    simp only [checkStepsK] at h
    apply checkStepsK_sound h a
    intro e he
    exact hst e (List.mem_filter.mp he).1

/-- The initial database: clause `i` (0-based) of the CNF gets LRAT id `i+1`. -/
def initK : Nat → List (CNF.Clause Nat) → KState
  | _, [] => []
  | i, c :: cs => (i, c.literals) :: initK (i + 1) cs

theorem mem_initK : ∀ {i : Nat} {cs : List (CNF.Clause Nat)} {e : Nat × KClause},
    e ∈ initK i cs → ∃ c ∈ cs, e.2 = c.literals
  | _, [], _, he => by cases he
  | i, c :: cs, e, he => by
    simp only [initK] at he
    rcases List.mem_cons.mp he with rfl | hrest
    · exact ⟨c, List.mem_cons_self .., rfl⟩
    · obtain ⟨c', hc', heq⟩ := mem_initK hrest
      exact ⟨c', List.mem_cons_of_mem _ hc', heq⟩

/-- Kernel-mode LRAT check: every reduction step is kernel-friendly, so
    `checkKernel cnf proof = true` can be discharged with `decide +kernel`. -/
def checkKernel (cnf : CNF Nat) (proof : List IntAction) : Bool :=
  checkStepsK (initK 1 cnf.clauses.toList) proof

theorem checkKernel_sound (cnf : CNF Nat) (proof : List IntAction)
    (h : checkKernel cnf proof = true) : cnf.Unsat := by
  intro a
  cases heval : CNF.eval a cnf with
  | false => rfl
  | true =>
    exfalso
    apply checkStepsK_sound h a
    intro e he
    obtain ⟨c, hc, he2⟩ := mem_initK he
    rw [he2]
    simp only [CNF.eval, Array.all_eq_true_iff_forall_mem] at heval
    exact heval c (Array.mem_toList_iff.mp hc)

end LRATCatcher
