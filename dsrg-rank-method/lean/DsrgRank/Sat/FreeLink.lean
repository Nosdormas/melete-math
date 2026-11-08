module

public import DsrgRank.Parts
public import DsrgRank.Sat.FreeFormula

/-!
Links the matrix of a DSRG to the variables of that formula: boolMat, the indicator ind, and the
counts of arcs and paths in each block (card_of_dsrg, fits_of_dsrg), so that the variables count the
arcs and paths of the matrix.
-/

@[expose] public section

set_option autoImplicit false

namespace DsrgRank.Sat.Free

open DsrgRank DsrgRank.Sat.Card

def boolMat (A : Mat) : Nat → Nat → Bool := fun i j => decide (A i j = 1)

def ind (b : Bool) : Int := if b then 1 else 0

theorem cnt_eq_sum {α : Type} (σ : α → Bool) (x : Nat → Lit α) :
    ∀ n, (cnt σ x n : Int) = sumBelow n (fun m => ind (litVal σ (x m)))
  | 0 => rfl
  | n + 1 => by
    rw [cnt_succ, sumBelow, ← cnt_eq_sum σ x n]
    simp only [ind]
    split <;> simp

theorem sumBelow_skip1 (g : Nat → Int) {i : Nat} :
    ∀ n, i ≤ n → sumBelow n (fun m => g (skip1 i m)) = sumBelow (n + 1) g - g i
  | 0, hi => by
    have : i = 0 := by omega
    subst this; simp [sumBelow]
  | n + 1, hi => by
    by_cases h : i ≤ n
    · have ih := sumBelow_skip1 g n h
      have hs : skip1 i n = n + 1 := by simp only [skip1]; split <;> omega
      show sumBelow n (fun m => g (skip1 i m)) + g (skip1 i n) = sumBelow (n + 1) g + g (n + 1) - g i
      rw [ih, hs]; omega
    · have hin : i = n + 1 := by omega
      subst hin
      have hc : sumBelow (n + 1) (fun m => g (skip1 (n + 1) m)) = sumBelow (n + 1) g :=
        sumBelow_congr (fun l hl => by simp [skip1, hl])
      rw [hc]
      show _ = sumBelow (n + 1) g + g (n + 1) - g (n + 1)
      omega

theorem sumBelow_skip1' {F g : Nat → Int} {i n : Nat} (hi : i ≤ n)
    (hF : ∀ m, m < n → F m = g (skip1 i m)) : sumBelow n F = sumBelow (n + 1) g - g i := by
  rw [sumBelow_congr hF]
  exact sumBelow_skip1 g n hi

theorem sumBelow_skip2' {F g : Nat → Int} {i j n : Nat} (hij : i ≠ j) (hi : i ≤ n + 1)
    (hj : j ≤ n + 1) (hF : ∀ m, m < n → F m = g (skip2 i j m)) :
    sumBelow n F = sumBelow (n + 2) g - g i - g j := by
  have e1 := sumBelow_skip1' (F := F) (g := fun l => g (skip1 (min i j) l)) (i := max i j - 1)
    (n := n) (by omega) (fun m hm => by rw [hF m hm]; simp [skip2, hij])
  have e2 := sumBelow_skip1' (F := fun l => g (skip1 (min i j) l)) (g := g) (i := min i j)
    (n := n + 1) (by omega) (fun m _ => rfl)
  have e3 : skip1 (min i j) (max i j - 1) = max i j := by simp only [skip1]; split <;> omega
  simp only [e3] at e1
  have e4 : sumBelow (n + 1 + 1) g = sumBelow (n + 2) g := rfl
  have e5 : g (min i j) + g (max i j) = g i + g j := by
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · rw [Nat.min_eq_left (Nat.le_of_lt h), Nat.max_eq_right (Nat.le_of_lt h)]
    · rw [Nat.min_eq_right (Nat.le_of_lt h), Nat.max_eq_left (Nat.le_of_lt h)]; omega
  rw [e1, e2, e4]
  omega

theorem skip1_lt {i m n : Nat} (hm : m < n) : skip1 i m < n + 1 := by
  simp only [skip1]; split <;> omega

theorem skip2_lt {i j m n : Nat} (hij : i ≠ j) (hm : m < n) : skip2 i j m < n + 2 := by
  simp only [skip2, hij, ite_false, skip1]; split <;> split <;> omega

theorem exists_skipF {v y j : Nat} (hy0 : 0 < y) (hyv : y < v) (hj0 : 0 < j) (hjv : j < v)
    (hjy : j ≠ y) : ∃ m, m < v - 2 ∧ skipF y m = j := by
  by_cases h : j < y
  · exact ⟨j - 1, by omega, by simp only [skipF, skip1]; split <;> omega⟩
  · exact ⟨j - 2, by omega, by simp only [skipF, skip1]; split <;> omega⟩

section Dsrg

variable {v k t lam mu : Nat} {A : Mat}

theorem ind_cell {a : Int} (h : a = 0 ∨ a = 1) : ind (decide (a = 1)) = a := by
  rcases h with rfl | rfl <;> rfl

theorem ind_path {a b : Int} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    ind (decide (a = 1) && decide (b = 1)) = a * b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rfl

theorem card_of_dsrg (h : IsDSRG v A k t lam mu) (b : Blk) (hb : b.valid ⟨v, k, t, lam, mu⟩ = true) :
    (∃ l, b.guardLit = some l ∧ litVal (base (boolMat A)) l = true) ∨
      cnt (base (boolMat A)) b.inputs (b.size ⟨v, k, t, lam, mu⟩) = b.bound ⟨v, k, t, lam, mu⟩ := by
  obtain ⟨h01, hdiag, hrow, hcol, hsq⟩ := h
  have hv : ∀ {i}, i < v → v - 1 + 1 = v := fun hi => by omega
  cases b with
  | out i =>
    simp only [Blk.valid, decide_eq_true_eq] at hb
    right
    simp only [Blk.size, Blk.bound]
    have e := cnt_eq_sum (base (boolMat A)) (Blk.out i).inputs (v - 1)
    rw [sumBelow_skip1' (g := fun l => A i l) (i := i) (n := v - 1) (by omega) (fun m hm => by
      simp only [Blk.inputs, litVal_pos, base, boolMat]
      exact ind_cell (h01 i hb _ (by have := skip1_lt (i := i) hm; omega))),
      hv hb, hrow i hb, hdiag i hb] at e
    omega
  | inn i =>
    simp only [Blk.valid, decide_eq_true_eq] at hb
    right
    simp only [Blk.size, Blk.bound]
    have e := cnt_eq_sum (base (boolMat A)) (Blk.inn i).inputs (v - 1)
    rw [sumBelow_skip1' (g := fun l => A l i) (i := i) (n := v - 1) (by omega) (fun m hm => by
      simp only [Blk.inputs, litVal_pos, base, boolMat]
      exact ind_cell (h01 _ (by have := skip1_lt (i := i) hm; omega) i hb)),
      hv hb, hcol i hb, hdiag i hb] at e
    omega
  | path i j g =>
    simp only [Blk.valid, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨hi, hj⟩, hg⟩ := hb
    have hind : ∀ m, skip2 i j m < v →
        ind (litVal (base (boolMat A)) ((Blk.path i j g).inputs m)) =
          (fun l => A i l * A l j) (skip2 i j m) := by
      intro m hx
      simp only [Blk.inputs, litVal_pos, base, boolMat]
      exact ind_path (h01 i hi _ hx) (h01 _ hx j hj)
    by_cases hij : i = j
    · subst hij
      simp only [ite_true, beq_iff_eq] at hg; subst hg
      right
      simp only [Blk.size, Blk.bound, ite_true]
      have e := cnt_eq_sum (base (boolMat A)) (Blk.path i i 0).inputs (v - 1)
      rw [sumBelow_skip1' (g := fun l => A i l * A l i) (i := i) (n := v - 1) (by omega) (fun m hm => by
        rw [hind m (by simp only [skip2, ite_true]; have := skip1_lt (i := i) hm; omega)]
        simp [skip2]), hv hi, hsq i hi i hi, hdiag i hi] at e
      simp [delta] at e
      omega
    · simp only [hij, ite_false, Bool.or_eq_true, beq_iff_eq] at hg
      have e := cnt_eq_sum (base (boolMat A)) (Blk.path i j g).inputs (v - 2)
      rw [sumBelow_skip2' (g := fun l => A i l * A l j) (n := v - 2) hij (by omega) (by omega) (fun m hm => by
        rw [hind m (by have := skip2_lt hij hm; omega)]), show v - 2 + 2 = v by omega,
        hsq i hi j hj, hdiag i hi, hdiag j hj] at e
      have hd : delta i j = 0 := by simp [delta, hij]
      rw [hd] at e
      rcases hg with rfl | rfl
      · rcases h01 i hi j hj with hz | ho
        · left
          exact ⟨_, rfl, by simp [litVal, base, boolMat, hz]⟩
        · right
          simp only [Blk.size, Blk.bound, hij, ite_false]
          rw [ho] at e; simp at e; omega
      · rcases h01 i hi j hj with hz | ho
        · right
          simp only [Blk.size, Blk.bound, hij, ite_false]
          rw [hz] at e; simp at e; omega
        · left
          exact ⟨_, rfl, by simp [litVal, base, boolMat, ho]⟩

theorem fits_of_dsrg (h : IsDSRG v A k t lam mu)
    (hcan : ∀ j, 0 < j → j < v →
      (A 0 j = 1 ↔ j ≤ k) ∧ (A j 0 = 1 ↔ (j ≤ t ∨ (k < j ∧ j ≤ 2 * k - t))))
    (hfree : ∀ y, 0 < y → y < v → A y 0 = 1 → A 0 y = 1 →
      ∃ j, 0 < j ∧ j < v ∧ j ≠ y ∧ ¬ (A y j = 1 ↔ A 0 j = 1)) :
    Fits ⟨v, k, t, lam, mu⟩ (boolMat A) where
  diag i hi := by simp [boolMat, h.2.1 i hi]
  card b hb := card_of_dsrg h b hb
  canon j h0 hj := by
    obtain ⟨e1, e2⟩ := hcan j h0 hj
    exact ⟨by simp only [boolMat]; exact decide_eq_decide.2 e1,
      by simp only [boolMat]; exact decide_eq_decide.2 e2⟩
  free y h0 hy hy0 h0y := by
    simp only [boolMat, decide_eq_true_eq] at hy0 h0y
    obtain ⟨j, hj0, hjv, hjy, hne⟩ := hfree y h0 hy hy0 h0y
    obtain ⟨m, hm, rfl⟩ := exists_skipF h0 hy hj0 hjv hjy
    refine ⟨m, hm, fun e => hne ?_⟩
    simp only [boolMat] at e
    exact decide_eq_decide.1 e

end Dsrg

end DsrgRank.Sat.Free
