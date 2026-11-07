import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import DsrgRank.Spectrum.Statement
import DsrgRank.Spectrum.Trace
import DsrgRank.Spectrum.Struct

namespace DsrgRank

theorem disc_identity {n : Nat} {k t lam mu : Int} {f g : Nat} {r s : ℝ}
    (hn : 1 ≤ n) (hfg : f + g = n - 1) (hsum : r + s = ((lam - mu : ℤ) : ℝ))
    (hprod : r * s = ((mu - t : ℤ) : ℝ)) (htr : (k : ℝ) + f * r + g * s = 0) :
    (2 * k + ((n : ℤ) - 1) * (lam - mu)) ^ 2 = ((f : ℤ) - g) ^ 2 * disc t lam mu := by
  have hn' : ((n : ℝ) - 1) = (f : ℝ) + g := by
    have : (n : ℕ) = f + g + 1 := by omega
    rw [this]; push_cast; ring
  have hX : (((2 * k + ((n : ℤ) - 1) * (lam - mu)) : ℤ) : ℝ) = ((g : ℝ) - f) * (r - s) := by
    push_cast at hsum ⊢
    linear_combination 2 * htr + ((lam : ℝ) - mu) * hn' - ((f : ℝ) + g) * hsum
  have hΔ : ((disc t lam mu : ℤ) : ℝ) = (r - s) ^ 2 := by
    unfold disc
    push_cast at hsum hprod ⊢
    linear_combination (-(r + s + ((lam : ℝ) - mu))) * hsum + 4 * hprod
  have : (((2 * k + ((n : ℤ) - 1) * (lam - mu)) ^ 2 : ℤ) : ℝ) =
      ((((f : ℤ) - g) ^ 2 * disc t lam mu : ℤ) : ℝ) := by
    rw [Int.cast_pow, hX, Int.cast_mul, hΔ]; push_cast; ring
  exact_mod_cast this

theorem rankBound_iff_two_min {n : Nat} {k t lam mu : Int} {R f g : Nat} {r s : ℝ}
    (hn : 1 ≤ n) (hfg : f + g = n - 1) (hsum : r + s = ((lam - mu : ℤ) : ℝ))
    (hprod : r * s = ((mu - t : ℤ) : ℝ)) (htr : (k : ℝ) + f * r + g * s = 0)
    (hpos : 0 < disc t lam mu) :
    RankBound n k t lam mu R ↔ R ≤ 2 * min f g := by
  have key := disc_identity hn hfg hsum hprod htr
  unfold RankBound
  rw [key]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : ((f : ℤ) - g) ^ 2 ≤ ((n : ℤ) - 1 - R) ^ 2 := le_of_mul_le_mul_right h2 hpos
    have h4 : |((f : ℤ) - g)| ≤ |((n : ℤ) - 1 - R)| := sq_le_sq.mp h3
    have h5 : |((n : ℤ) - 1 - R)| = (n : ℤ) - 1 - R := abs_of_nonneg (by omega)
    rw [h5] at h4
    have h6 := abs_le.mp h4
    omega
  · intro h
    refine ⟨by omega, ?_⟩
    apply mul_le_mul_of_nonneg_right _ (le_of_lt hpos)
    apply sq_le_sq' <;> omega

theorem rankBound_D {n : Nat} {A : Mat} {k t lam mu : Int} (h : IsDSRG n A k t lam mu)
    (hn : 0 < n) (hpos : 0 < disc t lam mu) : RankBound n k t lam mu (toQ n (D A)).rank := by
  obtain ⟨f, g, r, s, hfg, hsum, hprod, htr, hR⟩ := rank_D_parts h hn hpos
  exact (rankBound_iff_two_min hn hfg hsum hprod htr hpos).mpr hR

theorem SpectralLemma (n : Nat) (A : Mat) (k t lam mu : Int) (h : IsDSRG n A k t lam mu)
    (_hk : 0 < k) (hkn : k < (n : Int) - 1) (ht : 0 < t) (hκ : t < k) :
    SpectralLemmaStmt n A k t lam mu := by
  have hn : 0 < n := by omega
  exact ⟨rankBound_D h hn (disc_pos h ht hκ hkn), trace_bound h⟩

theorem SpectralLemma_full (n : Nat) (A : Mat) (k t lam mu : Int) (h : IsDSRG n A k t lam mu)
    (hk : 0 < k) (hkn : k < (n : Int) - 1) (ht : 0 < t) (hκ : t < k) :
    SpectralLemmaFull n A k t lam mu := by
  have hn : 0 < n := by omega
  exact ⟨SpectralLemma_struct h hn (disc_pos h ht hκ hkn), SpectralLemma n A k t lam mu h hk hkn ht hκ⟩

end DsrgRank
