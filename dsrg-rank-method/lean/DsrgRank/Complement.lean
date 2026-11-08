module

public import DsrgRank.ClosedNeighbourhood
public import DsrgRank.TwinClasses
public import DsrgRank.VertexFrame

/-!
Proves that the complement of a directed strongly regular graph with parameters (n, k, t, lambda,
mu) is one with complementary parameters, and uses this to exclude the complements of nine parameter
sets, among them (66, 55, 50, 45, 50) and (40, 30, 27, 21, 27).
-/

@[expose] public section

namespace DsrgRank

def complMat (A : Nat → Nat → Int) (i j : Nat) : Int := 1 - delta i j - A i j

theorem sumBelow_one (n : Nat) : sumBelow n (fun _ => (1 : Int)) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumBelow, ih]; push_cast; ring

theorem sumBelow_delta_row {n i : Nat} (hi : i < n) : sumBelow n (fun l => delta i l) = 1 := by
  rw [sumBelow_congr (g := fun l => if l = i then (1 : Int) else 0) (fun l _ => by
    unfold delta; by_cases h : l = i
    · simp [h]
    · simp [h, Ne.symm h])]
  exact sumBelow_single 1 hi

theorem sumBelow_delta_col {n j : Nat} (hj : j < n) : sumBelow n (fun l => delta l j) = 1 := by
  rw [sumBelow_congr (g := fun l => if l = j then (1 : Int) else 0) (fun l _ => by
    unfold delta; by_cases h : l = j <;> simp [h])]
  exact sumBelow_single 1 hj

theorem sumBelow_delta_left {n i : Nat} (hi : i < n) (f : Nat → Int) :
    sumBelow n (fun l => delta i l * f l) = f i := by
  rw [sumBelow_congr (g := fun l => if l = i then f i else 0) (fun l _ => by
    unfold delta; by_cases h : l = i
    · subst h; simp
    · simp [h, Ne.symm h])]
  exact sumBelow_single (f i) hi

theorem sumBelow_delta_right {n j : Nat} (hj : j < n) (f : Nat → Int) :
    sumBelow n (fun l => f l * delta l j) = f j := by
  rw [sumBelow_congr (g := fun l => if l = j then f j else 0) (fun l _ => by
    unfold delta; by_cases h : l = j
    · subst h; simp
    · simp [h])]
  exact sumBelow_single (f j) hj

theorem isDSRG_compl {n : Nat} {A : Nat → Nat → Int} {k t lam mu : Int}
    (h : IsDSRG n A k t lam mu) :
    IsDSRG n (complMat A) (n - k - 1) (n - 2 * k + t - 1) (n - 2 * k + mu - 2)
      (n - 2 * k + lam) := by
  obtain ⟨h01, hdiag, hrow, hcol, hsq⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj
    unfold complMat delta
    by_cases e : i = j
    · subst e; simp [hdiag i hi]
    · rcases h01 i hi j hj with h0 | h1
      · simp [e, h0]
      · simp [e, h1]
  · intro i hi
    simp [complMat, delta, hdiag i hi]
  · intro i hi
    have hr := hrow i hi
    have e : sumBelow n (fun j => complMat A i j) =
        sumBelow n (fun _ => (1 : Int)) - sumBelow n (fun j => delta i j) -
          sumBelow n (fun j => A i j) := by
      unfold complMat
      rw [← sumBelow_sub, ← sumBelow_sub]
    rw [e, sumBelow_one, sumBelow_delta_row hi, hr]
    ring
  · intro j hj
    have hc := hcol j hj
    have e : sumBelow n (fun i => complMat A i j) =
        sumBelow n (fun _ => (1 : Int)) - sumBelow n (fun i => delta i j) -
          sumBelow n (fun i => A i j) := by
      unfold complMat
      rw [← sumBelow_sub, ← sumBelow_sub]
    rw [e, sumBelow_one, sumBelow_delta_col hj, hc]
    ring
  · intro i hi j hj
    have hs := hsq i hi j hj
    have e : sumBelow n (fun l => complMat A i l * complMat A l j) =
        sumBelow n (fun _ => (1 : Int)) - sumBelow n (fun l => delta l j) -
          sumBelow n (fun l => A l j) - sumBelow n (fun l => delta i l) +
          sumBelow n (fun l => delta i l * delta l j) + sumBelow n (fun l => delta i l * A l j) -
          sumBelow n (fun l => A i l) + sumBelow n (fun l => A i l * delta l j) +
          sumBelow n (fun l => A i l * A l j) := by
      rw [← sumBelow_sub, ← sumBelow_sub, ← sumBelow_sub, ← sumBelow_add, ← sumBelow_add,
        ← sumBelow_sub, ← sumBelow_add, ← sumBelow_add]
      apply sumBelow_congr
      intro l _
      unfold complMat
      ring
    rw [e, sumBelow_one, sumBelow_delta_col hj, sumBelow_delta_row hi,
      sumBelow_delta_left hi, sumBelow_delta_left hi, sumBelow_delta_right hj, hcol j hj,
      hrow i hi, hs]
    unfold complMat
    ring

theorem not_isDSRG_compl {n : Nat} {k t lam mu : Int}
    (hno : ∀ A : Mat, ¬ IsDSRG n A k t lam mu) (A : Mat) :
    ¬ IsDSRG n A (n - k - 1) (n - 2 * k + t - 1) (n - 2 * k + mu - 2) (n - 2 * k + lam) := by
  intro h
  have h2 := isDSRG_compl h
  have e1 : (n : Int) - ((n : Int) - k - 1) - 1 = k := by ring
  have e2 : (n : Int) - 2 * ((n : Int) - k - 1) + ((n : Int) - 2 * k + t - 1) - 1 = t := by ring
  have e3 : (n : Int) - 2 * ((n : Int) - k - 1) + ((n : Int) - 2 * k + lam) - 2 = lam := by ring
  have e4 : (n : Int) - 2 * ((n : Int) - k - 1) + ((n : Int) - 2 * k + mu - 2) = mu := by ring
  rw [e1, e2, e3, e4] at h2
  exact hno _ h2

theorem compl_no_66_55_50_45_50 (A : Mat) : ¬ IsDSRG 66 A 55 50 45 50 := by
  have h := not_isDSRG_compl TwinMuOne_no_66_10_5_4_1 A
  norm_num at h
  exact h

theorem compl_no_91_78_72_66_72 (A : Mat) : ¬ IsDSRG 91 A 78 72 66 72 := by
  have h := not_isDSRG_compl TwinMuOne_no_91_12_6_5_1 A
  norm_num at h
  exact h

theorem compl_no_40_30_27_21_27 (A : Mat) : ¬ IsDSRG 40 A 30 27 21 27 := by
  have h := not_isDSRG_compl TwinMuOne_no_40_9_6_5_1 A
  norm_num at h
  exact h

theorem compl_no_96_80_75_65_75 (A : Mat) : ¬ IsDSRG 96 A 80 75 65 75 := by
  have h := not_isDSRG_compl TwinMuOne_no_96_15_10_9_1 A
  norm_num at h
  exact h

theorem compl_no_80_60_54_42_54 (A : Mat) : ¬ IsDSRG 80 A 60 54 42 54 := by
  have h := not_isDSRG_compl Twin_no_80_19_13_12_2 A
  norm_num at h
  exact h

theorem compl_no_50_38_34_29_28 (A : Mat) : ¬ IsDSRG 50 A 38 34 29 28 := by
  have h := not_isDSRG_compl ClosedNbhd_no_50_11_7_0_3 A
  norm_num at h
  exact h

theorem compl_no_68_54_48_43_42 (A : Mat) : ¬ IsDSRG 68 A 54 48 43 42 := by
  have h := not_isDSRG_compl ClosedNbhd_no_68_13_7_0_3 A
  norm_num at h
  exact h

theorem compl_no_100_83_74_69_68 (A : Mat) : ¬ IsDSRG 100 A 83 74 69 68 := by
  have h := not_isDSRG_compl ClosedNbhd_no_100_16_7_0_3 A
  norm_num at h
  exact h

theorem compl_no_108_88_78_72_70 (A : Mat) : ¬ IsDSRG 108 A 88 78 72 70 := by
  have h := not_isDSRG_compl ClosedNbhd_no_108_19_9_0_4 A
  norm_num at h
  exact h

theorem Case28_free_row (A : Mat) (h : IsDSRG 28 A 6 3 2 1) :
    ∃ B : Mat, IsDSRG 28 B 6 3 2 1 ∧ ∃ y : Fin 28, rowCl B y = {y} := by
  obtain ⟨y, hy | hy⟩ := VFrame_28 A h
  · exact ⟨A, h, y, hy⟩
  · exact ⟨transpose A, isDSRG_transpose h, y, hy⟩

end DsrgRank
