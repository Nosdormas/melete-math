import DsrgRank.Spectrum.Statement
import DsrgRank.Spectrum.Cert

namespace DsrgRank

open Matrix

theorem sumBelow_eq_range (n : Nat) (f : Nat → Int) :
    sumBelow n f = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumBelow, Finset.sum_range_succ, ih]

theorem sumBelow_eq_fin (n : Nat) (f : Nat → Int) : sumBelow n f = ∑ i : Fin n, f i := by
  rw [sumBelow_eq_range, Fin.sum_univ_eq_sum_range]

def toQr (m n : Nat) (M : Mat) : Matrix (Fin m) (Fin n) ℚ := Matrix.of fun i j => (M i j : ℚ)

theorem rank_le_of_factor {n R : Nat} {M B C : Mat} {d : Int} (h : FactorCert n R M B C d) :
    (toQ n M).rank ≤ R := by
  obtain ⟨hd, h⟩ := h
  have heq : (d : ℚ) • toQ n M = toQr n R B * toQr R n C := by
    ext i j
    have hij := h i i.isLt j j.isLt
    rw [sumBelow_eq_fin] at hij
    simp only [Matrix.smul_apply, toQ, toQr, Matrix.of_apply, Matrix.mul_apply, smul_eq_mul]
    exact_mod_cast hij
  have hdq : (d : ℚ) ∈ nonZeroDivisors ℚ :=
    mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hd)
  rw [← Matrix.rank_smul_of_mem_nonZeroDivisors _ hdq, heq]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

theorem le_rank_of_minor {n R : Nat} {M P Q : Mat} {d : Int} (h : MinorCert n R M P Q d) :
    R ≤ (toQ n M).rank := by
  obtain ⟨hd, h⟩ := h
  have heq : toQr R n P * (toQ n M * toQr n R Q) = (d : ℚ) • (1 : Matrix (Fin R) (Fin R) ℚ) := by
    ext a b
    have hab := h a a.isLt b b.isLt
    simp only [sumBelow_eq_fin] at hab
    simp only [Matrix.mul_apply, toQ, toQr, Matrix.of_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    by_cases e : a = b
    · subst e
      simp only [delta, ite_true] at hab
      simp only [ite_true]
      exact_mod_cast hab
    · have e' : (a : Nat) ≠ b := Fin.val_ne_iff.mpr e
      simp only [delta, e', ite_false] at hab
      simp only [e, ite_false]
      exact_mod_cast hab
  have hdq : (d : ℚ) ∈ nonZeroDivisors ℚ :=
    mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hd)
  have hr : ((d : ℚ) • (1 : Matrix (Fin R) (Fin R) ℚ)).rank = R := by
    rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ hdq, Matrix.rank_one, Fintype.card_fin]
  calc R = (toQr R n P * (toQ n M * toQr n R Q)).rank := by rw [heq, hr]
    _ ≤ (toQ n M * toQr n R Q).rank := Matrix.rank_mul_le_right _ _
    _ ≤ (toQ n M).rank := Matrix.rank_mul_le_left _ _

theorem RankBound.mono {n : Nat} {k t lam mu : Int} {R R' : Nat} (hΔ : 0 ≤ disc t lam mu)
    (h : RankBound n k t lam mu R') (hR : R ≤ R') : RankBound n k t lam mu R := by
  obtain ⟨h1, h2⟩ := h
  have hR' : (R : Int) ≤ R' := by exact_mod_cast hR
  refine ⟨by omega, h2.trans ?_⟩
  apply Int.mul_le_mul_of_nonneg_right _ hΔ
  have h0 : 0 ≤ (n : Int) - 1 - R' := by omega
  have h3 : (n : Int) - 1 - R' ≤ (n : Int) - 1 - R := by omega
  nlinarith

theorem SpectralLemmaStmt_of_cert (n : Nat) (A : Mat) (k t lam mu : Int) (R₁ : Nat) (B C : Mat) (d₁ : Int)
    (R₂ : Nat) (P Q : Mat) (d₂ : Int) (h : SpectralLemmaCert n A k t lam mu R₁ B C d₁ R₂ P Q d₂) :
    SpectralLemmaStmt n A k t lam mu := by
  obtain ⟨hf, hm, hb, hΔ, htr0, htr⟩ := h
  have hup := rank_le_of_factor hf
  have hlo : (R₂ : Int) ≤ ((toQ n (D A)).rank : Int) := by exact_mod_cast le_rank_of_minor hm
  exact ⟨RankBound.mono hΔ hb hup, htr.trans (Int.mul_le_mul_of_nonneg_right hlo htr0)⟩

def SpectralLemmaHalfStmt (n : Nat) (A : Mat) (k t lam mu : Int) : Prop :=
  RankBound n k t lam mu (2 * (toQ n (D A)).rank)

theorem not_SpectralLemmaHalf_of_refutation (n : Nat) (A : Mat) (k t lam mu : Int) (R₂ : Nat) (P Q : Mat)
    (d₂ : Int) (h : SpectralLemmaHalfRefutation n A k t lam mu R₂ P Q d₂) : ¬ SpectralLemmaHalfStmt n A k t lam mu := by
  obtain ⟨hm, hΔ, hbad⟩ := h
  intro hr
  exact hbad (RankBound.mono hΔ hr (Nat.mul_le_mul_left 2 (le_rank_of_minor hm)))

end DsrgRank
