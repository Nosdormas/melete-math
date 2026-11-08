module

public import DsrgRank.ClosedNeighbourhood
public import DsrgRank.Graphs.Small

/-!
Example file that applies the lambda = 0 closed-neighbourhood bound to explicit matrices of known
DSRGs with parameters (6, 2, 1, 0, 1), (18, 4, 3, 0, 1) and (16, 5, 5, 0, 2), so that the hypotheses
of these theorems are shown to be satisfiable.
-/

@[expose] public section

set_option autoImplicit false

namespace DsrgRank.ClosedNbhdExamples

open DsrgRank

abbrev A6 : Mat := ofBitmasks [6, 17, 40, 17, 40, 6]

theorem h6 : IsDSRG 6 A6 2 1 0 1 := DsrgRank.Graphs.Small.g_6_2_1_0_1_0

theorem disc6 : disc 1 0 1 = 1 := by decide

theorem roots6 : IsRootPair 1 0 1 (-1 : ℝ) 0 := by
  unfold IsRootPair; norm_num

theorem ClosedNbhd_live6 : (2 : Int) * 2 - 1 ≤ (Module.finrank ℝ (eigA 6 A6 0) : ℤ) :=
  ClosedNbhd_bound h6 (by decide) (by decide) (by decide) roots6 (by norm_num) (by norm_num)

theorem dimE0_6 : Module.finrank ℝ (eigA 6 A6 0) = 3 := by
  have hr : rR 1 0 1 = 0 := by unfold rR; rw [disc6]; norm_num
  have hs : sR 1 0 1 = -1 := by unfold sR; rw [disc6]; norm_num
  obtain ⟨-, -, hsum, htr⟩ := spectrum_counts h6 (by decide) (by decide) (by decide)
  rw [hr, hs] at hsum htr
  generalize Module.finrank ℝ ↥(eigA 6 A6 0) = F at hsum htr ⊢
  generalize Module.finrank ℝ ↥(eigA 6 A6 (-1)) = G at hsum htr ⊢
  have hG : (G : ℝ) = 2 := by push_cast at htr; linarith
  have hG' : G = 2 := by exact_mod_cast hG
  omega

theorem ClosedNbhd_tight6 : (2 : Int) * 2 - 1 = (Module.finrank ℝ (eigA 6 A6 0) : ℤ) := by
  rw [dimE0_6]; norm_num

theorem ClosedNbhd_bound_plus_one_false6 : ¬ ((2 : Int) * 2 - 1 + 1 ≤ (Module.finrank ℝ (eigA 6 A6 0) : ℤ)) := by
  rw [dimE0_6]; norm_num

theorem card6 : ((nbhd 6 A6 0).card : ℤ) = 4 := by
  rw [ClosedNbhd_card h6 0]; norm_num

abbrev A18 : Mat := ofBitmasks [586, 2340, 1169, 36881, 147492, 73738, 139393, 69892, 49218,
  82945, 43012, 135682, 10376, 17504, 4880, 66824, 131744, 34896]

theorem h18 : IsDSRG 18 A18 4 3 0 1 := DsrgRank.Graphs.Small.g_18_4_3_0_1_1

theorem ClosedNbhd_r_one_live18 : ((2 : Int) * 4 - 3) * (1 + 2) ≤ 4 + 18 - 1 :=
  ClosedNbhd_r_one h18 (by decide) (by decide) (by decide)

theorem ClosedNbhd_live18 :
    (2 : Int) * 4 - 3 ≤ (Module.finrank ℝ (eigA 18 A18 (-2)) : ℤ) ∧
      (2 : Int) * 4 - 3 ≤ (Module.finrank ℝ (eigA 18 A18 1) : ℤ) := by
  refine ⟨?_, ?_⟩
  · exact ClosedNbhd_bound (θ := 1) (θ' := -2) h18 (by decide) (by decide) (by decide)
      (by unfold IsRootPair; norm_num) (by norm_num) (by norm_num)
  · exact ClosedNbhd_bound (θ := -2) (θ' := 1) h18 (by decide) (by decide) (by decide)
      (by unfold IsRootPair; norm_num) (by norm_num) (by norm_num)

abbrev A16 : Mat := ofBitmasks [24770, 36913, 24632, 37060, 1670, 2374, 1577, 2329, 42144, 43088,
  20816, 21152, 11274, 4869, 35845, 17162]

theorem h16 : IsDSRG 16 A16 5 5 0 2 := by decide +kernel

theorem ClosedNbhd_r_one_live16 : ((2 : Int) * 5 - 5) * (2 + 2) ≤ 5 + 16 - 1 :=
  ClosedNbhd_r_one h16 (by decide) (by decide) (by decide)

theorem ClosedNbhd_r_one_strict_false16 :
    ¬ (∀ (n : Nat) (A : Mat) (k t mu : Int), IsDSRG n A k t 0 mu → 0 < n → 0 < mu →
      t = 2 * mu + 1 → (2 * k - t) * (mu + 2) < k + n - 1) := by
  intro hall
  have := hall 16 A16 5 5 2 h16 (by decide) (by decide) (by decide)
  norm_num at this

theorem ClosedNbhd_no_54_13_9_0_4 (A : Mat) : ¬ IsDSRG 54 A 13 9 0 4 := by
  intro h; have := ClosedNbhd_r_one h (by norm_num) (by norm_num) (by norm_num); norm_num at this

theorem ClosedNbhd_no_64_17_13_0_6 (A : Mat) : ¬ IsDSRG 64 A 17 13 0 6 := by
  intro h; have := ClosedNbhd_r_one h (by norm_num) (by norm_num) (by norm_num); norm_num at this

theorem ClosedNbhd_no_70_15_9_0_4 (A : Mat) : ¬ IsDSRG 70 A 15 9 0 4 := by
  intro h; have := ClosedNbhd_r_one h (by norm_num) (by norm_num) (by norm_num); norm_num at this

theorem ClosedNbhd_no_78_19_13_0_6 (A : Mat) : ¬ IsDSRG 78 A 19 13 0 6 := by
  intro h; have := ClosedNbhd_r_one h (by norm_num) (by norm_num) (by norm_num); norm_num at this

theorem ClosedNbhd_no_88_23_17_0_8 (A : Mat) : ¬ IsDSRG 88 A 23 17 0 8 := by
  intro h; have := ClosedNbhd_r_one h (by norm_num) (by norm_num) (by norm_num); norm_num at this

theorem ClosedNbhd_no_110_31_25_0_12 (A : Mat) : ¬ IsDSRG 110 A 31 25 0 12 := by
  intro h; have := ClosedNbhd_r_one h (by norm_num) (by norm_num) (by norm_num); norm_num at this

end DsrgRank.ClosedNbhdExamples

#print axioms DsrgRank.ClosedNbhdExamples.ClosedNbhd_live6
#print axioms DsrgRank.ClosedNbhdExamples.ClosedNbhd_tight6
#print axioms DsrgRank.ClosedNbhdExamples.ClosedNbhd_bound_plus_one_false6
#print axioms DsrgRank.ClosedNbhdExamples.ClosedNbhd_r_one_live18
#print axioms DsrgRank.ClosedNbhdExamples.ClosedNbhd_live18
#print axioms DsrgRank.ClosedNbhdExamples.ClosedNbhd_r_one_live16
#print axioms DsrgRank.ClosedNbhdExamples.ClosedNbhd_r_one_strict_false16
#print axioms DsrgRank.ClosedNbhdExamples.ClosedNbhd_no_54_13_9_0_4
#print axioms DsrgRank.ClosedNbhdExamples.ClosedNbhd_no_110_31_25_0_12
