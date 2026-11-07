import DsrgRank.TwinClassesMuOne
import DsrgRank.TwinClasses
import DsrgRank.Graphs.Small

set_option autoImplicit false

namespace DsrgRank.TwinExamples

open DsrgRank Matrix

example : ∀ A : Mat, ¬ IsDSRG 66 A 10 5 4 1 := TwinMuOne_no_66_10_5_4_1
example : ∀ A : Mat, ¬ IsDSRG 91 A 12 6 5 1 := TwinMuOne_no_91_12_6_5_1
example : ∀ A : Mat, ¬ IsDSRG 40 A 9 6 5 1 := TwinMuOne_no_40_9_6_5_1
example : ∀ A : Mat, ¬ IsDSRG 96 A 15 10 9 1 := TwinMuOne_no_96_15_10_9_1
example : ∀ A : Mat, ¬ IsDSRG 80 A 19 13 12 2 := Twin_no_80_19_13_12_2

abbrev A8 : Mat := ofBitmasks [14, 13, 81, 162, 69, 138, 176, 112]

theorem h8 : IsDSRG 8 A8 3 2 1 1 := DsrgRank.Graphs.Small.g_8_3_2_1_1_2

/-- (15, 4, 2, 1, 1), `triangle-controls.json#15-4-2-1-1-2`: `k = 2λ + 2`, `λ = 1`. -/
abbrev A15 : Mat := ofBitmasks [30, 29, 1601, 6304, 24834, 4613, 1541, 16410, 24594, 20640, 10560,
  1224, 10528, 6432, 1728]

theorem h15 : IsDSRG 15 A15 4 2 1 1 := by
  decide +kernel

abbrev A16 : Mat := ofBitmasks [254, 253, 251, 6961, 239, 6937, 58502, 58438, 6713, 6457, 64256,
  63232, 61184, 57088, 42182, 25798]

theorem h16 : IsDSRG 16 A16 7 5 4 2 := by
  decide +kernel

abbrev A45 : Mat := ofBitmasks [510, 1838597, 8455716867, 503, 14708776, 3908420239384, 447,
  117670208, 31267361915072, 261120, 1837575, 541165880832, 257536, 14700600, 30787265114112,
  228864, 117604800, 3855806988288, 133693440, 1314311, 34634617061376, 131858432, 10514488,
  488558821376, 117178368, 84115904, 61119397888, 8321499143, 30786996695040, 60649635840,
  7381975047, 486419726336, 3851512152064, 532575948288, 3891240370232, 26826768384, 472446406144,
  351128256512, 30992484008384, 34084862296064, 2808908611640, 1656783863808, 30236571598848,
  21991172108288, 13675175870912]

theorem h45 : IsDSRG 45 A45 8 4 3 1 := by
  decide +kernel

theorem a8 : (rowCl A8 (0 : Fin 8)).card = 2 := by decide +kernel
theorem d8 : (colCl A8 (0 : Fin 8)).card = 2 := by decide +kernel
theorem a15 : (rowCl A15 (3 : Fin 15)).card = 1 := by decide +kernel
theorem a16 : (rowCl A16 (0 : Fin 16)).card = 4 := by decide +kernel

theorem f8 : Module.finrank ℝ (eigA 8 A8 ((1 : Int) : ℝ)) = 2 := by
  have e := (TwinMuOne_spec h8 (by norm_num) (by norm_num) (by norm_num)).2
  omega

theorem TwinMuOne_live8 : True := by
  have _h1 := TwinMuOne_inter h8 (by norm_num) (0 : Fin 8) (0 : Fin 8)
  have _h2 := TwinMuOne_class h8 (by norm_num) (by norm_num) (0 : Fin 8)
  have _h3 := TwinMuOne_ad h8 (by norm_num) (by norm_num) (0 : Fin 8)
  have _h4 := TwinMuOne_rank h8 (by norm_num) (by norm_num) (0 : Fin 8)
  have _h5 := TwinMuOne_admissible h8 (by norm_num) (by norm_num) (by norm_num) (0 : Fin 8)
  trivial

theorem TwinMuOne_class_tight8 :
    ((rowCl A8 (0 : Fin 8)).card : Int) * (1 + 2 - (rowCl A8 (0 : Fin 8)).card) =
      3 + 1 - (rowCl A8 (0 : Fin 8)).card := by
  rw [a8]; norm_num

theorem TwinMuOne_ad_tight8 :
    ((rowCl A8 (0 : Fin 8)).card : Int) + (colCl A8 (0 : Fin 8)).card = 1 + 3 := by
  rw [a8, d8]; norm_num

theorem TwinMuOne_rank_tight8 :
    ((rowCl A8 (0 : Fin 8)).card : Int) = 3 + 1 - (Module.finrank ℝ (eigA 8 A8 ((1 : Int) : ℝ)) : Int) := by
  rw [a8, f8]; norm_num

theorem TwinMuOne_free_live45 : ∀ z : Fin 45, 2 ≤ (rowCl A45 z).card ∧ 2 ≤ (colCl A45 z).card :=
  fun z => ⟨TwinMuOne_free_twin h45 (by norm_num) (by norm_num) (by norm_num) z,
    TwinMuOne_free_twin_col h45 (by norm_num) (by norm_num) (by norm_num) z⟩

theorem f16 : Module.finrank ℝ (eigA 16 A16 (((4 : Int) : ℝ) + 1 - ((2 : Int) : ℝ))) = 2 := by
  have e := (Twin_spec h16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
  omega

theorem Twin_live16 : True := by
  have _h0 := Twin_inter h16 (by norm_num) (0 : Fin 16) (0 : Fin 16)
  have _h1 := Twin_le h16 (by norm_num) (by norm_num) (0 : Fin 16)
  have _h3 := Twin_class h16 (by norm_num) (0 : Fin 16)
  have _h4 := Twin_lower h16 (by norm_num) (0 : Fin 16)
  have _h5 := Twin_upper h16 (by norm_num) (by norm_num) (0 : Fin 16)
  have _h6 := Twin_cond h16 (by norm_num) (by norm_num) (by norm_num) (0 : Fin 16)
  have _ha := Twin_admissible h16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (0 : Fin 16)
  trivial

theorem Twin_upper_tight16 : ((rowCl A16 (0 : Fin 16)).card : Int) = 7 - 4 - 1 + 2 := by
  rw [a16]; norm_num

theorem Twin_lower_tight16 :
    7 + 1 - ((rowCl A16 (0 : Fin 16)).card : Int) =
      2 * (Module.finrank ℝ (eigA 16 A16 (((4 : Int) : ℝ) + 1 - ((2 : Int) : ℝ))) : Int) := by
  rw [a16, f16]; norm_num

theorem Twin_upper_minus_false :
    ¬ ∀ (n : Nat) (A : Mat) (k t lam mu : Int), IsDSRG n A k t lam mu → t = lam + 1 → t < k →
      ∀ x : Fin n, ((rowCl A x).card : Int) ≤ k - lam - 2 + mu := by
  intro H
  have e := H 16 A16 7 5 4 2 h16 (by norm_num) (by norm_num) 0
  rw [a16] at e
  norm_num at e

theorem Twin_cond_strict_false :
    ¬ ∀ (n : Nat) (A : Mat) (k t lam mu : Int), IsDSRG n A k t lam mu → t = lam + 1 → t < k →
      mu < lam + 2 → Fin n → (lam + 2 - mu) ^ 2 < mu * ((n : Int) - 1 - k) := by
  intro H
  have e := H 8 A8 3 2 1 1 h8 (by norm_num) (by norm_num) (by norm_num) 0
  norm_num at e

theorem Twin_lower_plus_false :
    ¬ ∀ (n : Nat) (A : Mat) (k t lam mu : Int), IsDSRG n A k t lam mu → t = lam + 1 →
      ∀ x : Fin n, (lam + 2 - mu) * (k + 2 - (rowCl A x).card) ≤ mu * ((n : Int) - (k + 1)) := by
  intro H
  have e := H 16 A16 7 5 4 2 h16 (by norm_num) 0
  rw [a16] at e
  norm_num at e

theorem TwinMuOne_free_twin_thr1_false :
    ¬ ∀ (n : Nat) (A : Mat) (k t lam : Int), IsDSRG n A k t lam 1 → t = lam + 1 → k = 2 * lam + 2 →
      1 ≤ lam → ∀ x : Fin n, 2 ≤ (rowCl A x).card := by
  intro H
  have e := H 15 A15 4 2 1 h15 (by norm_num) (by norm_num) (by norm_num) 3
  rw [a15] at e
  omega

theorem TwinMuOne_family_thr3_false :
    ¬ ∀ (n : Nat) (A : Mat) (k t lam : Int), IsDSRG n A k t lam 1 → t = lam + 1 → k = 2 * lam + 2 →
      3 ≤ lam → (∀ z : Fin n, 2 ≤ (rowCl A z).card) → (∀ z : Fin n, 2 ≤ (colCl A z).card) →
      Fin n → False := by
  intro H
  exact H 45 A45 8 4 3 h45 (by norm_num) (by norm_num) (by norm_num)
    (fun z => (TwinMuOne_free_live45 z).1) (fun z => (TwinMuOne_free_live45 z).2) 0

theorem TwinMuOne_class_minus_false :
    ¬ ∀ (n : Nat) (A : Mat) (k t lam : Int), IsDSRG n A k t lam 1 → t = lam + 1 → t < k →
      ∀ x : Fin n, ((rowCl A x).card : Int) * (lam + 2 - (rowCl A x).card) ≤ k - (rowCl A x).card := by
  intro H
  have e := H 8 A8 3 2 1 h8 (by norm_num) (by norm_num) 0
  rw [a8] at e
  norm_num at e

theorem TwinMuOne_rank_plus_false :
    ¬ ∀ (n : Nat) (A : Mat) (k t lam : Int), IsDSRG n A k t lam 1 → t = lam + 1 → 0 ≤ lam →
      ∀ x : Fin n, k + 2 - (Module.finrank ℝ (eigA n A (lam : ℝ)) : Int) ≤ (rowCl A x).card := by
  intro H
  have e := H 8 A8 3 2 1 h8 (by norm_num) (by norm_num) 0
  rw [a8, f8] at e
  norm_num at e

end DsrgRank.TwinExamples

#print axioms DsrgRank.TwinExamples.h45
#print axioms DsrgRank.TwinExamples.TwinMuOne_live8
#print axioms DsrgRank.TwinExamples.TwinMuOne_free_live45
#print axioms DsrgRank.TwinExamples.Twin_live16
#print axioms DsrgRank.TwinExamples.Twin_upper_minus_false
#print axioms DsrgRank.TwinExamples.Twin_cond_strict_false
#print axioms DsrgRank.TwinExamples.Twin_lower_plus_false
#print axioms DsrgRank.TwinExamples.TwinMuOne_free_twin_thr1_false
#print axioms DsrgRank.TwinExamples.TwinMuOne_family_thr3_false
#print axioms DsrgRank.TwinExamples.TwinMuOne_class_minus_false
#print axioms DsrgRank.TwinExamples.TwinMuOne_rank_plus_false
