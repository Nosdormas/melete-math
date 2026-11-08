module

public import DsrgRank.Sat.SeqCounter

/-!
Writes, for parameters (v, k, t, lambda, mu), a CNF formula with cardinality constraints for a DSRG
with a vertex whose row twin class is a single vertex. It proves that the matrix of such a DSRG
satisfies the formula (formula_sat) and that the clause checker checkNat is sound (checkNat_sound).
-/

@[expose] public section

namespace DsrgRank.Sat.Free

open DsrgRank.Sat.Card

structure Params where
  v : Nat
  k : Nat
  t : Nat
  lam : Nat
  mu : Nat
deriving Repr, DecidableEq

inductive Blk where
  | out (i : Nat)
  | inn (i : Nat)
  | path (i j g : Nat)
deriving DecidableEq, Repr

inductive FVar where
  | a (i j : Nat)
  | p (i x j : Nat)
  | c (b : Blk) (most : Bool) (d j : Nat)
  | r (y j : Nat)
deriving DecidableEq, Repr

def skip1 (i m : Nat) : Nat := if m < i then m else m + 1

def skip2 (i j m : Nat) : Nat :=
  if i = j then skip1 i m else skip1 (min i j) (skip1 (max i j - 1) m)

def skipF (y m : Nat) : Nat := skip1 y (m + 1)

namespace Blk

def size (P : Params) : Blk → Nat
  | out _ => P.v - 1
  | inn _ => P.v - 1
  | path i j _ => if i = j then P.v - 1 else P.v - 2

def bound (P : Params) : Blk → Nat
  | out _ => P.k
  | inn _ => P.k
  | path _ _ 0 => P.t
  | path _ _ 1 => P.lam
  | path _ _ _ => P.mu

def inputs : Blk → Nat → Lit FVar
  | out i, m => (.a i (skip1 i m), true)
  | inn i, m => (.a (skip1 i m) i, true)
  | path i j _, m => (.p i (skip2 i j m) j, true)

def guardLit : Blk → Option (Lit FVar)
  | path i j 1 => some (.a i j, false)
  | path i j 2 => some (.a i j, true)
  | _ => none

def valid (P : Params) : Blk → Bool
  | out i => decide (i < P.v)
  | inn i => decide (i < P.v)
  | path i j g => decide (i < P.v) && decide (j < P.v) && (if i = j then g == 0 else g == 1 || g == 2)

def partInputs (b : Blk) (most : Bool) : Nat → Lit FVar := if most then b.inputs else negs b.inputs

def partBound (P : Params) (b : Blk) (most : Bool) : Nat :=
  if most then b.bound P else b.size P - b.bound P

def clauses (P : Params) (b : Blk) : List (Cl FVar) :=
  guard b.guardLit (equals (FVar.c b false) (FVar.c b true) b.inputs (b.size P) (b.bound P))

end Blk

def pathCl (i x j : Nat) : List (Cl FVar) :=
  [[(.p i x j, false), (.a i x, true)], [(.p i x j, false), (.a x j, true)],
   [(.p i x j, true), (.a i x, false), (.a x j, false)]]

def pathBlock (P : Params) (i j : Nat) : List (Cl FVar) :=
  ((List.range ((Blk.path i j 0).size P)).flatMap fun m => pathCl i (skip2 i j m) j) ++
  (if i = j then (Blk.path i i 0).clauses P
   else (Blk.path i j 1).clauses P ++ (Blk.path i j 2).clauses P)

def symCl (P : Params) (j : Nat) : List (Cl FVar) :=
  [[(.a 0 j, decide (j ≤ P.k))],
   [(.a j 0, decide (j ≤ P.t ∨ (P.k < j ∧ j ≤ 2 * P.k - P.t)))]]

/-- `r(y, j) → a(y, j) ≠ a(0, j)`. -/
def diffCl (y j : Nat) : List (Cl FVar) :=
  [[(.r y j, false), (.a y j, true), (.a 0 j, true)],
   [(.r y j, false), (.a y j, false), (.a 0 j, false)]]

def bigCl (P : Params) (y : Nat) : Cl FVar :=
  [(.a y 0, false), (.a 0 y, false)] ++ (List.range (P.v - 2)).map fun m => (.r y (skipF y m), true)

def freeBlock (P : Params) (y : Nat) : List (Cl FVar) :=
  ((List.range (P.v - 2)).flatMap fun m => diffCl y (skipF y m)) ++ [bigCl P y]

def formula (P : Params) : List (Cl FVar) :=
  ((List.range P.v).map fun i => [(.a i i, false)]) ++
  ((List.range P.v).flatMap fun i => (Blk.out i).clauses P ++ (Blk.inn i).clauses P) ++
  ((List.range P.v).flatMap fun i => (List.range P.v).flatMap fun j => pathBlock P i j) ++
  ((List.range (P.v - 1)).flatMap fun m => symCl P (m + 1)) ++
  ((List.range (P.v - 1)).flatMap fun m => freeBlock P (m + 1))

def aux (n b : Nat) : Nat := if General n b then (n - b) * b else 0

def auxE (n b : Nat) : Nat := aux n (n - b) + aux n b

def nodeOff (b d j : Nat) : Nat :=
  if d = 0 then 2 * j - 2 else if d = 1 then 2 * j - 1 else d * b + j - 1

namespace Params

def Ek (P : Params) : Nat := auxE (P.v - 1) P.k

def rowStart (P : Params) (i : Nat) : Nat := P.v + 2 * i * P.Ek + i * (2 * P.v - 1 - i)

def p0 (P : Params) : Nat := P.rowStart P.v

def P0 (P : Params) : Nat := (P.v - 1) + auxE (P.v - 1) P.t

def P1 (P : Params) : Nat := (P.v - 2) + auxE (P.v - 2) P.lam + auxE (P.v - 2) P.mu

def PR (P : Params) : Nat := (P.v - 1) * P.P1 + P.P0

def pathStart (P : Params) (i j : Nat) : Nat :=
  P.p0 + i * P.PR + (if j ≤ i then j * P.P1 else (j - 1) * P.P1 + P.P0)

def f0 (P : Params) : Nat := P.p0 + P.v * P.PR

def top (P : Params) : Nat := P.f0 + (P.v - 1) * (P.v - 2)

end Params

def auxBase (P : Params) : Blk → Bool → Nat
  | .out i, most => P.rowStart i + (P.v - 1 - i) + (if most then aux (P.v - 1) (P.v - 1 - P.k) else 0)
  | .inn i, most => P.rowStart i + 2 * (P.v - 1 - i) + P.Ek +
      (if most then aux (P.v - 1) (P.v - 1 - P.k) else 0)
  | .path i j g, most =>
      let n := (Blk.path i j g).size P
      P.pathStart i j + n + (if g = 2 then auxE n P.lam else 0) +
        (if most then aux n (n - (Blk.path i j g).bound P) else 0)

def num (P : Params) : FVar → Nat
  | .a i j =>
    if i = j then i + 1
    else if i < j then P.rowStart i + (j - i)
    else P.rowStart j + (P.v - 1 - j) + P.Ek + (i - j)
  | .p i x j => P.pathStart i j + 1 + x - (if i < x then 1 else 0) - (if j < x ∧ j ≠ i then 1 else 0)
  | .c b most d j => auxBase P b most + 1 + nodeOff (b.partBound P most) d j
  | .r y j => P.f0 + (y - 1) * (P.v - 2) + (j - 1) - (if y < j then 1 else 0) + 1

def decNode (b o : Nat) : Nat × Nat :=
  if o < 2 * b then (o % 2, o / 2 + 1) else (o / b, o % b + 1)

def decPart (P : Params) (blk : Blk) (o : Nat) : FVar :=
  let n := blk.size P
  let bL := n - blk.bound P
  if o < aux n bL then FVar.c blk false (decNode bL o).1 (decNode bL o).2
  else FVar.c blk true (decNode (blk.bound P) (o - aux n bL)).1 (decNode (blk.bound P) (o - aux n bL)).2

def decRow (P : Params) (i o : Nat) : FVar :=
  let w := P.v - 1 - i
  if o < w then .a i (i + 1 + o)
  else if o < w + P.Ek then decPart P (.out i) (o - w)
  else if o < 2 * w + P.Ek then .a (i + 1 + (o - w - P.Ek)) i
  else decPart P (.inn i) (o - 2 * w - P.Ek)

def findRow (P : Params) (n : Nat) : Nat → Nat → Nat
  | i, 0 => i
  | i, fuel + 1 => if n ≤ P.rowStart (i + 1) then i else findRow P n (i + 1) fuel

def decPathBlock (P : Params) (i j o : Nat) : FVar :=
  let n := (Blk.path i j 0).size P
  if o < n then .p i (skip2 i j o) j
  else if i = j then decPart P (.path i i 0) (o - n)
  else if o - n < auxE n P.lam then decPart P (.path i j 1) (o - n)
  else decPart P (.path i j 2) (o - n - auxE n P.lam)

def decPath (P : Params) (q : Nat) : FVar :=
  let i := q / P.PR
  let o := q % P.PR
  if o < i * P.P1 then decPathBlock P i (o / P.P1) (o % P.P1)
  else if o < i * P.P1 + P.P0 then decPathBlock P i i (o - i * P.P1)
  else decPathBlock P i (i + 1 + (o - i * P.P1 - P.P0) / P.P1) ((o - i * P.P1 - P.P0) % P.P1)

def dec (P : Params) (n : Nat) : FVar :=
  if n ≤ P.v then .a (n - 1) (n - 1)
  else if n ≤ P.p0 then
    decRow P (findRow P n 0 P.v) (n - P.rowStart (findRow P n 0 P.v) - 1)
  else if n ≤ P.f0 then decPath P (n - P.p0 - 1)
  else .r ((n - P.f0 - 1) / (P.v - 2) + 1) (skipF ((n - P.f0 - 1) / (P.v - 2) + 1) ((n - P.f0 - 1) % (P.v - 2)))

def formulaNat (P : Params) : List (List (Nat × Bool)) :=
  (formula P).map fun c => c.map fun l => (num P l.1 - 1, l.2)

def writeDimacs (P : Params) (path : System.FilePath) : IO Unit := do
  let cls := formulaNat P
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  h.putStr s!"p cnf {P.top} {cls.length}\n"
  for c in cls do
    let body := " ".intercalate (c.map fun l => if l.2 then toString (l.1 + 1) else s!"-{l.1 + 1}")
    h.putStr (if c.isEmpty then "0\n" else body ++ " 0\n")
  h.flush

def cardDimacs (kind : String) (lits : List Int) (b top : Nat) : List (List Int) :=
  let n := lits.length
  let x : Nat → Lit Nat := fun m => let l := lits.getD m 0; (l.natAbs, decide (0 < l))
  let sAt (base bb : Nat) : Nat → Nat → Nat := fun d j => base + 1 + nodeOff bb d j
  let cls :=
    if kind = "atmost" then atmost (sAt top b) x n b
    else if kind = "atleast" then atleast (sAt top (n - b)) x n b
    else equals (sAt top (n - b)) (sAt (top + aux n (n - b)) b) x n b
  cls.map fun c => c.map fun l => if l.2 then (l.1 : Int) else -(l.1 : Int)

def decMisses (P : Params) : Nat :=
  ((formula P).map fun c => (c.filter fun l => dec P (num P l.1) != l.1).length).foldl (· + ·) 0

def base (B : Nat → Nat → Bool) : FVar → Bool
  | .a i j => B i j
  | .p i x j => B i x && B x j
  | .r y j => B y j != B 0 j
  | .c .. => false

def sigma (B : Nat → Nat → Bool) : FVar → Bool
  | .c b most d j => counterVal (base B) (b.partInputs most) d j
  | v => base B v

structure Fits (P : Params) (B : Nat → Nat → Bool) : Prop where
  diag : ∀ i, i < P.v → B i i = false
  card : ∀ b : Blk, b.valid P = true →
    (∃ l, b.guardLit = some l ∧ litVal (base B) l = true) ∨
      cnt (base B) b.inputs (b.size P) = b.bound P
  canon : ∀ j, 0 < j → j < P.v →
    B 0 j = decide (j ≤ P.k) ∧ B j 0 = decide (j ≤ P.t ∨ (P.k < j ∧ j ≤ 2 * P.k - P.t))
  free : ∀ y, 0 < y → y < P.v → B y 0 = true → B 0 y = true →
    ∃ m, m < P.v - 2 ∧ B y (skipF y m) ≠ B 0 (skipF y m)

variable {P : Params} {B : Nat → Nat → Bool}

theorem sigma_a (i j : Nat) : sigma B (.a i j) = B i j := rfl
theorem sigma_p (i x j : Nat) : sigma B (.p i x j) = (B i x && B x j) := rfl
theorem sigma_r (y j : Nat) : sigma B (.r y j) = (B y j != B 0 j) := rfl

theorem inputs_val (b : Blk) (most : Bool) (m : Nat) :
    litVal (sigma B) (b.partInputs most m) = litVal (base B) (b.partInputs most m) := by
  cases most <;> cases b <;> simp [Blk.partInputs, Blk.inputs, negs, neg, litVal, sigma, base]

theorem cnt_sigma (b : Blk) (most : Bool) (n : Nat) :
    cnt (sigma B) (b.partInputs most) n = cnt (base B) (b.partInputs most) n :=
  cnt_congr (fun m => inputs_val b most m) n

theorem hs_sigma (b : Blk) (most : Bool) :
    ∀ d j, sigma B (FVar.c b most d j) = counterVal (sigma B) (b.partInputs most) d j := by
  intro d j
  simp only [sigma, counterVal, cnt_sigma]

theorem guardLit_val (b : Blk) (l : Lit FVar) (h : b.guardLit = some l) :
    litVal (sigma B) l = litVal (base B) l := by
  cases b with
  | out i => simp [Blk.guardLit] at h
  | inn i => simp [Blk.guardLit] at h
  | path i j g =>
    rcases g with _ | _ | _ | g
    · simp [Blk.guardLit] at h
    · simp only [Blk.guardLit, Option.some.injEq] at h; subst h; rfl
    · simp only [Blk.guardLit, Option.some.injEq] at h; subst h; rfl
    · simp [Blk.guardLit] at h

theorem part_cnt (b : Blk) (most : Bool) (h : cnt (base B) b.inputs (b.size P) = b.bound P) :
    cnt (sigma B) (b.partInputs most) (b.size P) = b.partBound P most := by
  rw [cnt_sigma]
  cases most
  · simp [Blk.partInputs, Blk.partBound, cnt_negs, h]
  · simp [Blk.partInputs, Blk.partBound, h]

theorem guard_or_cnt (h : Fits P B) (b : Blk) (hb : b.valid P = true) :
    (∃ l, b.guardLit = some l ∧ litVal (sigma B) l = true) ∨
      cnt (base B) b.inputs (b.size P) = b.bound P := by
  rcases h.card b hb with ⟨l, hl, hv⟩ | hc
  · exact Or.inl ⟨l, hl, by rw [guardLit_val b l hl]; exact hv⟩
  · exact Or.inr hc

theorem blk_sat (h : Fits P B) (b : Blk) (hb : b.valid P = true) :
    ∀ c ∈ b.clauses P, clTrue (sigma B) c = true := by
  apply guard_sat
  rcases guard_or_cnt h b hb with hg | hc
  · exact Or.inl hg
  · refine Or.inr (equals_sat ?_ ?_ ?_)
    · have := part_cnt (P := P) b true hc
      simpa [Blk.partInputs, Blk.partBound] using this
    · intro d j; rw [hs_sigma b false]; rfl
    · intro d j; rw [hs_sigma b true]; rfl

theorem pathCl_sat (i x j : Nat) : ∀ c ∈ pathCl i x j, clTrue (sigma B) c = true := by
  intro c hc
  simp only [pathCl, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl <;>
    simp only [clTrue, List.any_cons, List.any_nil, litVal_pos, litVal_negv, sigma_a, sigma_p] <;>
    cases B i x <;> cases B x j <;> rfl

theorem diffCl_sat (y j : Nat) : ∀ c ∈ diffCl y j, clTrue (sigma B) c = true := by
  intro c hc
  simp only [diffCl, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl <;>
    simp only [clTrue, List.any_cons, List.any_nil, litVal_pos, litVal_negv, sigma_a, sigma_r] <;>
    cases B y j <;> cases B 0 j <;> rfl

theorem symCl_sat (h : Fits P B) {j : Nat} (h0 : 0 < j) (hj : j < P.v) :
    ∀ c ∈ symCl P j, clTrue (sigma B) c = true := by
  intro c hc
  obtain ⟨e1, e2⟩ := h.canon j h0 hj
  simp only [symCl, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl
  · simp [clTrue, litVal, sigma_a, e1]
  · simp [clTrue, litVal, sigma_a, e2]

theorem bigCl_sat (h : Fits P B) {y : Nat} (h0 : 0 < y) (hy : y < P.v) :
    clTrue (sigma B) (bigCl P y) = true := by
  simp only [bigCl, clTrue_append]
  cases hy0 : B y 0
  · simp [clTrue, litVal, sigma_a, hy0]
  · cases h0y : B 0 y
    · simp [clTrue, litVal, sigma_a, h0y]
    · obtain ⟨m, hm, hne⟩ := h.free y h0 hy hy0 h0y
      have hr : sigma B (.r y (skipF y m)) = true := by
        rw [sigma_r]; cases e1 : B y (skipF y m) <;> cases e2 : B 0 (skipF y m) <;> simp_all
      simp only [Bool.or_eq_true]
      right
      simp only [clTrue, List.any_map, List.any_eq_true, List.mem_range]
      exact ⟨m, hm, by simp [Function.comp, litVal, hr]⟩

theorem formula_sat (h : Fits P B) : ∀ c ∈ formula P, clTrue (sigma B) c = true := by
  intro c hc
  simp only [formula, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at hc
  rcases hc with (((⟨i, hi, rfl⟩ | ⟨i, hi, hc⟩) | ⟨i, hi, j, hj, hc⟩) | ⟨m, hm, hc⟩) | ⟨m, hm, hc⟩
  · simp [clTrue, litVal, sigma_a, h.diag i hi]
  · rcases hc with hc | hc
    · exact blk_sat h (.out i) (by simp [Blk.valid, hi]) c hc
    · exact blk_sat h (.inn i) (by simp [Blk.valid, hi]) c hc
  · simp only [pathBlock, List.mem_append, List.mem_flatMap, List.mem_range] at hc
    rcases hc with ⟨m, _, hc⟩ | hc
    · exact pathCl_sat _ _ _ c hc
    · split at hc
      · rename_i hij; subst hij
        exact blk_sat h (.path i i 0) (by simp [Blk.valid, hi]) c hc
      · rename_i hij
        rcases List.mem_append.1 hc with hc | hc
        · exact blk_sat h (.path i j 1) (by simp [Blk.valid, hi, hj, hij]) c hc
        · exact blk_sat h (.path i j 2) (by simp [Blk.valid, hi, hj, hij]) c hc
  · exact symCl_sat h (by omega) (by omega) c hc
  · simp only [freeBlock, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_singleton] at hc
    rcases hc with ⟨m', _, hc⟩ | rfl
    · exact diffCl_sat _ _ c hc
    · exact bigCl_sat h (by omega) (by omega)

inductive Fam where
  | diag (i : Nat)
  | node (b : Blk) (most : Bool) (d j : Nat)
  | special (b : Blk) (most : Bool)
  | path (i x j : Nat)
  | sym (j : Nat)
  | diff (y j : Nat)
  | big (y : Nat)
deriving DecidableEq, Repr

namespace Fam

def clauses (P : Params) : Fam → List (Cl FVar)
  | diag i => [[(.a i i, false)]]
  | node b most d j =>
    guard b.guardLit (Card.node (FVar.c b most) (b.partInputs most) (b.partBound P most)
      (b.size P - 1 - b.partBound P most) d j)
  | special b most => guard b.guardLit (Card.special (b.partInputs most) (b.size P) (b.partBound P most))
  | path i x j => pathCl i x j
  | sym j => symCl P j
  | diff y j => diffCl y j
  | big y => [bigCl P y]

def valid (P : Params) : Fam → Bool
  | diag i => decide (i < P.v)
  | node b most d j =>
    b.valid P && decide (General (b.size P) (b.partBound P most)) &&
      decide (d ≤ b.size P - 1 - b.partBound P most) && decide (1 ≤ j) && decide (j ≤ b.partBound P most)
  | special b most => b.valid P && decide (b.partBound P most < b.size P)
  | path _ _ _ => true
  | sym j => decide (0 < j) && decide (j < P.v)
  | diff _ _ => true
  | big y => decide (0 < y) && decide (y < P.v)

end Fam

def cands : FVar → List Fam
  | .a i j => [.diag i, .sym j, .sym i, .special (.out i) false, .special (.out i) true,
      .special (.inn j) false, .special (.inn j) true]
  | .p i x j => [.path i x j, .special (.path i j 0) false, .special (.path i j 0) true,
      .special (.path i j 1) false, .special (.path i j 1) true,
      .special (.path i j 2) false, .special (.path i j 2) true]
  | .c b most d j => [.node b most d j, .node b most (d - 1) j, .node b most d (j - 1)]
  | .r y j => [.diff y j, .big y]

def check (P : Params) (c : Cl FVar) : Bool :=
  c.any fun l => (cands l.1).any fun F => F.valid P && (F.clauses P).contains c

theorem fam_sat (h : Fits P B) (F : Fam) (hF : F.valid P = true) :
    ∀ c ∈ F.clauses P, clTrue (sigma B) c = true := by
  cases F with
  | diag i =>
    intro c hc
    simp only [Fam.clauses, List.mem_singleton] at hc; subst hc
    simp only [Fam.valid, decide_eq_true_eq] at hF
    simp [clTrue, litVal, sigma_a, h.diag i hF]
  | node b most d j =>
    simp only [Fam.valid, Bool.and_eq_true, decide_eq_true_eq] at hF
    obtain ⟨⟨⟨⟨hb, hg⟩, hd⟩, hj1⟩, hjb⟩ := hF
    apply guard_sat
    rcases guard_or_cnt h b hb with hgd | hc
    · exact Or.inl hgd
    · exact Or.inr (node_sat (Nat.le_of_eq (part_cnt b most hc)) (hs_sigma b most) hd hj1 hjb hg)
  | special b most =>
    simp only [Fam.valid, Bool.and_eq_true, decide_eq_true_eq] at hF
    obtain ⟨hb, hlt⟩ := hF
    apply guard_sat
    rcases guard_or_cnt h b hb with hgd | hc
    · exact Or.inl hgd
    · exact Or.inr (special_sat (Nat.le_of_eq (part_cnt b most hc)) hlt)
  | path i x j => exact pathCl_sat i x j
  | sym j =>
    simp only [Fam.valid, Bool.and_eq_true, decide_eq_true_eq] at hF
    exact symCl_sat h hF.1 hF.2
  | diff y j => exact diffCl_sat y j
  | big y =>
    simp only [Fam.valid, Bool.and_eq_true, decide_eq_true_eq] at hF
    intro c hc
    simp only [Fam.clauses, List.mem_singleton] at hc; subst hc
    exact bigCl_sat h hF.1 hF.2

theorem check_sound (h : Fits P B) {c : Cl FVar} (hc : check P c = true) :
    clTrue (sigma B) c = true := by
  simp only [check, List.any_eq_true, Bool.and_eq_true, List.contains_iff_mem] at hc
  obtain ⟨_, _, F, _, hF, hmem⟩ := hc
  exact fam_sat h F hF c hmem

def checkNat (P : Params) (c : List (Nat × Bool)) : Bool :=
  check P (c.map fun l => (dec P (l.1 + 1), l.2))

theorem checkNat_sound (h : Fits P B) {c : List (Nat × Bool)} (hc : checkNat P c = true) :
    (c.any fun l => sigma B (dec P (l.1 + 1)) == l.2) = true := by
  have := check_sound h hc
  simpa [clTrue, litVal, List.any_map, Function.comp] using this

end DsrgRank.Sat.Free
