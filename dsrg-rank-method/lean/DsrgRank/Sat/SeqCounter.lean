

module

/-!
Sequential-counter encoding of at-most, at-least and exact-count constraints on the number of true
literals. It defines the clauses and proves that they are satisfied when the count meets the bound
(atmost_sat, atleast_sat, equals_sat).
-/

@[expose] public section

namespace DsrgRank.Sat.Card

abbrev Lit (α : Type) := α × Bool

abbrev Cl (α : Type) := List (Lit α)

variable {α : Type}

def litVal (σ : α → Bool) (l : Lit α) : Bool := σ l.1 == l.2

def clTrue (σ : α → Bool) (c : Cl α) : Bool := c.any (litVal σ)

def neg (l : Lit α) : Lit α := (l.1, !l.2)

def negs (x : Nat → Lit α) : Nat → Lit α := fun m => neg (x m)

def cnt (σ : α → Bool) (x : Nat → Lit α) : Nat → Nat
  | 0 => 0
  | m + 1 => cnt σ x m + (if litVal σ (x m) then 1 else 0)

def counterVal (σ : α → Bool) (x : Nat → Lit α) (d j : Nat) : Bool := decide (j ≤ cnt σ x (d + j))

def node (s : Nat → Nat → α) (x : Nat → Lit α) (b D d j : Nat) : List (Cl α) :=
  (if j = 1 then [[neg (x d), (s d 1, true)]] else []) ++
  (if d < D then [[(s d j, false), (s (d + 1) j, true)]] else []) ++
  (if j < b then [[neg (x (d + j)), (s d j, false), (s d (j + 1), true)]]
   else [[neg (x (d + j)), (s d j, false)]])

def special (x : Nat → Lit α) (n b : Nat) : List (Cl α) :=
  if b = 0 then (List.range n).map (fun m => [neg (x m)])
  else if b + 1 = n then [(List.range n).map (fun m => neg (x m))]
  else []

def General (n b : Nat) : Prop := 1 ≤ b ∧ b + 2 ≤ n

instance (n b : Nat) : Decidable (General n b) := by unfold General; infer_instance

def atmost (s : Nat → Nat → α) (x : Nat → Lit α) (n b : Nat) : List (Cl α) :=
  if n = 0 ∨ n ≤ b then []
  else if General n b then
    (List.range (n - b)).flatMap fun d => (List.range b).flatMap fun j => node s x b (n - 1 - b) d (j + 1)
  else special x n b

def atleast (s : Nat → Nat → α) (x : Nat → Lit α) (n b : Nat) : List (Cl α) :=
  atmost s (negs x) n (n - b)

def equals (sL sM : Nat → Nat → α) (x : Nat → Lit α) (n b : Nat) : List (Cl α) :=
  atleast sL x n b ++ atmost sM x n b

def guard : Option (Lit α) → List (Cl α) → List (Cl α)
  | none, cs => cs
  | some g, cs => cs.map (· ++ [g])

variable {σ : α → Bool} {x : Nat → Lit α}

@[simp] theorem litVal_neg (l : Lit α) : litVal σ (neg l) = !litVal σ l := by
  obtain ⟨v, b⟩ := l
  simp only [litVal, neg]
  cases σ v <;> cases b <;> rfl

theorem clTrue_append (c d : Cl α) : clTrue σ (c ++ d) = (clTrue σ c || clTrue σ d) := by
  simp [clTrue, List.any_append]

theorem cnt_succ (m : Nat) : cnt σ x (m + 1) = cnt σ x m + (if litVal σ (x m) then 1 else 0) := rfl

theorem cnt_le_self : ∀ m, cnt σ x m ≤ m
  | 0 => Nat.le_refl 0
  | m + 1 => by
    have := cnt_le_self m
    rw [cnt_succ]; split <;> omega

theorem cnt_mono {m m' : Nat} (h : m ≤ m') : cnt σ x m ≤ cnt σ x m' := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [cnt_succ]; omega

theorem cnt_add_neg : ∀ m, cnt σ x m + cnt σ (negs x) m = m
  | 0 => rfl
  | m + 1 => by
    have := cnt_add_neg m
    rw [cnt_succ, cnt_succ]
    simp only [negs, litVal_neg]
    cases litVal σ (x m) <;> simp <;> omega

theorem cnt_negs (m : Nat) : cnt σ (negs x) m = m - cnt σ x m := by
  have := cnt_add_neg (σ := σ) (x := x) m
  omega

theorem cnt_congr {τ : α → Bool} (h : ∀ m, litVal σ (x m) = litVal τ (x m)) :
    ∀ m, cnt σ x m = cnt τ x m
  | 0 => rfl
  | m + 1 => by rw [cnt_succ, cnt_succ, h m, cnt_congr h m]

theorem exists_false_of_cnt_lt {n : Nat} (h : cnt σ x n < n) : ∃ m, m < n ∧ litVal σ (x m) = false := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [cnt_succ] at h
    cases hx : litVal σ (x n) with
    | false => exact ⟨n, by omega, hx⟩
    | true =>
      simp only [hx, ite_true] at h
      obtain ⟨m, hm, hv⟩ := ih (by omega)
      exact ⟨m, by omega, hv⟩

theorem false_of_cnt_zero {n m : Nat} (h : cnt σ x n = 0) (hm : m < n) : litVal σ (x m) = false := by
  have h1 : cnt σ x (m + 1) ≤ cnt σ x n := cnt_mono hm
  rw [cnt_succ] at h1
  cases hx : litVal σ (x m) with
  | false => rfl
  | true => simp only [hx, ite_true] at h1; omega

@[simp] theorem litVal_pos (v : α) : litVal σ (v, true) = σ v := by
  simp only [litVal]; cases σ v <;> rfl

@[simp] theorem litVal_negv (v : α) : litVal σ (v, false) = !σ v := by
  simp only [litVal]; cases σ v <;> rfl

theorem node_sat {s : Nat → Nat → α} {n b d j : Nat} (hn : cnt σ x n ≤ b)
    (hs : ∀ d j, σ (s d j) = counterVal σ x d j) (hd : d ≤ n - 1 - b) (hj1 : 1 ≤ j) (hjb : j ≤ b)
    (hg : General n b) : ∀ c ∈ node s x b (n - 1 - b) d j, clTrue σ c = true := by
  intro c hc
  unfold General at hg
  simp only [node, List.mem_append] at hc
  have hsv : ∀ d j, σ (s d j) = decide (j ≤ cnt σ x (d + j)) := fun d j => hs d j
  rcases hc with (hc | hc) | hc
  · split at hc
    · rename_i hj; subst hj
      simp only [List.mem_singleton] at hc; subst hc
      simp only [clTrue, List.any_cons, List.any_nil, litVal_neg, litVal_pos, hsv, Bool.or_false]
      have := cnt_succ (σ := σ) (x := x) d
      cases hx : litVal σ (x d)
      · simp
      · simp only [hx, ite_true] at this
        simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq]
        omega
    · simp at hc
  · split at hc
    · simp only [List.mem_singleton] at hc; subst hc
      simp only [clTrue, List.any_cons, List.any_nil, litVal_negv, litVal_pos, hsv, Bool.or_false]
      have : cnt σ x (d + j) ≤ cnt σ x (d + 1 + j) := cnt_mono (by omega)
      by_cases h : j ≤ cnt σ x (d + j)
      · have h' : j ≤ cnt σ x (d + 1 + j) := by omega
        simp [h']
      · simp [h]
    · simp at hc
  · have hstep := cnt_succ (σ := σ) (x := x) (d + j)
    split at hc
    · simp only [List.mem_singleton] at hc; subst hc
      simp only [clTrue, List.any_cons, List.any_nil, litVal_neg, litVal_negv, litVal_pos, hsv,
        Bool.or_false]
      have e : d + (j + 1) = d + j + 1 := by omega
      rw [e]
      cases hx : litVal σ (x (d + j))
      · simp
      · simp only [hx, ite_true] at hstep
        by_cases h : j ≤ cnt σ x (d + j)
        · have h' : j + 1 ≤ cnt σ x (d + j + 1) := by omega
          simp [h']
        · simp [h]
    · simp only [List.mem_singleton] at hc; subst hc
      simp only [clTrue, List.any_cons, List.any_nil, litVal_neg, litVal_negv, hsv, Bool.or_false]
      have hle : cnt σ x (d + j + 1) ≤ cnt σ x n := cnt_mono (by omega)
      cases hx : litVal σ (x (d + j))
      · simp
      · simp only [hx, ite_true] at hstep
        have hnot : ¬ j ≤ cnt σ x (d + j) := by omega
        simp [hnot]

theorem special_sat {n b : Nat} (hn : cnt σ x n ≤ b) (hb : b < n) :
    ∀ c ∈ special x n b, clTrue σ c = true := by
  intro c hc
  simp only [special] at hc
  split at hc
  · subst_vars
    simp only [List.mem_map, List.mem_range] at hc
    obtain ⟨m, hm, rfl⟩ := hc
    have := false_of_cnt_zero (σ := σ) (x := x) (by omega) hm
    simp [clTrue, this]
  · split at hc
    · simp only [List.mem_singleton] at hc; subst hc
      obtain ⟨m, hm, hv⟩ := exists_false_of_cnt_lt (σ := σ) (x := x) (n := n) (by omega)
      simp only [clTrue, List.any_map, List.any_eq_true, List.mem_range]
      exact ⟨m, hm, by simp [Function.comp, hv]⟩
    · simp at hc

theorem atmost_sat {s : Nat → Nat → α} {n b : Nat} (hn : cnt σ x n ≤ b)
    (hs : ∀ d j, σ (s d j) = counterVal σ x d j) : ∀ c ∈ atmost s x n b, clTrue σ c = true := by
  intro c hc
  simp only [atmost] at hc
  split at hc
  · simp at hc
  · rename_i h0
    split at hc
    · rename_i hg
      simp only [List.mem_flatMap, List.mem_range] at hc
      obtain ⟨d, hd, j, hj, hc⟩ := hc
      exact node_sat hn hs (by unfold General at hg; omega) (by omega) (by omega) hg c hc
    · exact special_sat hn (by omega) c hc

theorem atleast_sat {s : Nat → Nat → α} {n b : Nat} (hn : b ≤ cnt σ x n)
    (hs : ∀ d j, σ (s d j) = counterVal σ (negs x) d j) : ∀ c ∈ atleast s x n b, clTrue σ c = true := by
  apply atmost_sat _ hs
  rw [cnt_negs]
  omega

theorem equals_sat {sL sM : Nat → Nat → α} {n b : Nat} (hn : cnt σ x n = b)
    (hL : ∀ d j, σ (sL d j) = counterVal σ (negs x) d j)
    (hM : ∀ d j, σ (sM d j) = counterVal σ x d j) : ∀ c ∈ equals sL sM x n b, clTrue σ c = true := by
  intro c hc
  simp only [equals, List.mem_append] at hc
  rcases hc with hc | hc
  · exact atleast_sat (by omega) hL c hc
  · exact atmost_sat (by omega) hM c hc

theorem guard_sat {g : Option (Lit α)} {cs : List (Cl α)}
    (h : (∃ l, g = some l ∧ litVal σ l = true) ∨ ∀ c ∈ cs, clTrue σ c = true) :
    ∀ c ∈ guard g cs, clTrue σ c = true := by
  intro c hc
  cases g with
  | none =>
    rcases h with ⟨l, hl, _⟩ | h
    · cases hl
    · exact h c hc
  | some l =>
    simp only [guard, List.mem_map] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    rw [clTrue_append]
    rcases h with ⟨l', hl, hv⟩ | h
    · cases hl
      simp [clTrue, hv]
    · simp [h c' hc']

end DsrgRank.Sat.Card
