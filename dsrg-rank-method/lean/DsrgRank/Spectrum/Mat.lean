module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import DsrgRank.Spectrum.Bridge

/-!
Defines the real matrices used by the spectral lemma: the all-ones matrix Jr, the projection Pi1 = I
- Jr/n, and Mp = 2A - (lambda - mu)I - betaR Jr, with their product and trace identities.
-/

@[expose] public section

set_option autoImplicit false

namespace DsrgRank

open Matrix

def Jr (n : Nat) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun _ _ => 1

noncomputable def Pi1 (n : Nat) : Matrix (Fin n) (Fin n) ℝ := 1 - (1 / (n : ℝ)) • Jr n

def aR (lam mu : Int) : ℝ := (lam : ℝ) - mu

/-- `β = (2k − a)/n`. -/
noncomputable def betaR (n : Nat) (k lam mu : Int) : ℝ := (2 * (k : ℝ) - aR lam mu) / n

/-- `M' = 2A − aI − βJ`. -/
noncomputable def Mp (n : Nat) (A : Mat) (k lam mu : Int) : Matrix (Fin n) (Fin n) ℝ :=
  (2 : ℝ) • toR n A - aR lam mu • (1 : Matrix (Fin n) (Fin n) ℝ) - betaR n k lam mu • Jr n

section

variable {n : Nat} {A : Mat} {k t lam mu : Int}

theorem Jr_mul_Jr : Jr n * Jr n = (n : ℝ) • Jr n := by
  ext i j; simp [Jr, Matrix.mul_apply]

theorem toR_sq (h : IsDSRG n A k t lam mu) :
    toR n A * toR n A = (t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) + (lam : ℝ) • toR n A +
      (mu : ℝ) • (Jr n - 1 - toR n A) := by
  ext i j
  have hij := h.2.2.2.2 i i.isLt j j.isLt
  rw [sumBelow_eq_fin] at hij
  have hR := congrArg (fun z : ℤ => (z : ℝ)) hij
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_one] at hR
  simp only [toR, Jr, Matrix.mul_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
  rw [hR]
  by_cases e : i = j
  · subst e; simp [delta]
  · have e' : (i : Nat) ≠ j := Fin.val_ne_iff.mpr e
    simp [delta, e, e']

theorem toR_mul_Jr (h : IsDSRG n A k t lam mu) : toR n A * Jr n = (k : ℝ) • Jr n := by
  ext i j
  have hi := h.2.2.1 i i.isLt
  rw [sumBelow_eq_fin] at hi
  have hR := congrArg (fun z : ℤ => (z : ℝ)) hi
  simp only [Int.cast_sum] at hR
  simp [toR, Jr, Matrix.mul_apply, hR]

theorem Jr_mul_toR (h : IsDSRG n A k t lam mu) : Jr n * toR n A = (k : ℝ) • Jr n := by
  ext i j
  have hj := h.2.2.2.1 j j.isLt
  rw [sumBelow_eq_fin] at hj
  have hR := congrArg (fun z : ℤ => (z : ℝ)) hj
  simp only [Int.cast_sum] at hR
  simp [toR, Jr, Matrix.mul_apply, hR]

theorem trace_toR (h : IsDSRG n A k t lam mu) : (toR n A).trace = 0 := by
  simp [Matrix.trace, toR, h.2.1 _ (Fin.isLt _)]

theorem trace_Jr : (Jr n).trace = n := by simp [Matrix.trace, Jr]

theorem k_sq (h : IsDSRG n A k t lam mu) (hn : 0 < n) :
    (k : ℝ) ^ 2 = t + lam * k + mu * ((n : ℝ) - 1 - k) := by
  have e1 : toR n A * toR n A * Jr n = ((k : ℝ) ^ 2) • Jr n := by
    rw [Matrix.mul_assoc, toR_mul_Jr h, Matrix.mul_smul, toR_mul_Jr h, smul_smul, sq]
  have e2 : toR n A * toR n A * Jr n =
      ((t : ℝ) + lam * k + mu * ((n : ℝ) - 1 - k)) • Jr n := by
    rw [toR_sq h]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
      Jr_mul_Jr, toR_mul_Jr h]
    module
  have := congrFun (congrFun (e1.symm.trans e2) ⟨0, hn⟩) ⟨0, hn⟩
  simpa [Jr] using this

theorem Mp_mul_Jr (h : IsDSRG n A k t lam mu) (hn : 0 < n) : Mp n A k lam mu * Jr n = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Mp, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, toR_mul_Jr h, Jr_mul_Jr]
  rw [smul_smul, smul_smul, ← sub_smul, ← sub_smul]
  convert zero_smul ℝ (Jr n)
  unfold betaR; field_simp; ring

theorem Jr_mul_Mp (h : IsDSRG n A k t lam mu) (hn : 0 < n) : Jr n * Mp n A k lam mu = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Mp, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Jr_mul_toR h, Jr_mul_Jr]
  rw [smul_smul, smul_smul, ← sub_smul, ← sub_smul]
  convert zero_smul ℝ (Jr n)
  unfold betaR; field_simp; ring

/-- `M'² = Δ(I − J/n)`. -/
theorem Mp_sq (h : IsDSRG n A k t lam mu) (hn : 0 < n) :
    Mp n A k lam mu * Mp n A k lam mu = (disc t lam mu : ℝ) • Pi1 n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hk := k_sq h hn
  unfold Mp Pi1
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, toR_sq h, Jr_mul_toR h, toR_mul_Jr h, Jr_mul_Jr, smul_sub,
    smul_add, smul_smul]
  simp only [disc, Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_ofNat]
  match_scalars <;> simp only [aR, betaR] <;> field_simp <;>
    first
    | ring1
    | linear_combination 4 * hk
    | linear_combination (-4) * hk

theorem Jr_transpose : (Jr n)ᵀ = Jr n := by ext i j; simp [Jr]

theorem Pi1_transpose : (Pi1 n)ᵀ = Pi1 n := by
  simp [Pi1, Matrix.transpose_sub, Matrix.transpose_smul, Jr_transpose]

theorem Pi1_mul_Pi1 (hn : 0 < n) : Pi1 n * Pi1 n = Pi1 n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Pi1, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Jr_mul_Jr, smul_smul]
  match_scalars <;> field_simp <;> ring1

theorem toRT_mul_Jr (h : IsDSRG n A k t lam mu) : (toR n A)ᵀ * Jr n = (k : ℝ) • Jr n := by
  have := congrArg Matrix.transpose (Jr_mul_toR h)
  simpa [Matrix.transpose_mul, Jr_transpose, Matrix.transpose_smul] using this

theorem Jr_mul_toRT (h : IsDSRG n A k t lam mu) : Jr n * (toR n A)ᵀ = (k : ℝ) • Jr n := by
  have := congrArg Matrix.transpose (toR_mul_Jr h)
  simpa [Matrix.transpose_mul, Jr_transpose, Matrix.transpose_smul] using this

end

end DsrgRank
