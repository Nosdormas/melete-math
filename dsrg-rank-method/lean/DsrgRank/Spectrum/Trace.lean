module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Algebra.Order.Chebyshev
public import DsrgRank.Spectrum.RankLemmas

/-!
Proves that for a Hermitian matrix G, (tr G)^2 is at most rank G times tr(G^2), and applies this to
D D^T to get trace_bound, the trace inequality of the spectral lemma.
-/

@[expose] public section

set_option autoImplicit false

namespace DsrgRank

open Matrix

theorem trace_sq_le_rank_mul {m : Nat} (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.IsHermitian) :
    G.trace ^ 2 ≤ (G.rank : ℝ) * (G * G).trace := by
  classical
  set ev := hG.eigenvalues with hev
  have htr : G.trace = ∑ i, ev i := by
    simpa [RCLike.ofReal_real_eq_id] using hG.trace_eq_sum_eigenvalues
  have hrk : G.rank = Fintype.card {i // ev i ≠ 0} := hG.rank_eq_card_non_zero_eigs
  have htr2 : (G * G).trace = ∑ i, ev i ^ 2 := by
    have hs := hG.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    set Um : Matrix (Fin m) (Fin m) ℝ := (hG.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)
    have hUU : star Um * Um = 1 := Unitary.coe_star_mul_self hG.eigenvectorUnitary
    set d : Matrix (Fin m) (Fin m) ℝ := diagonal (RCLike.ofReal ∘ hG.eigenvalues)
    have hGG : G * G = Um * (d * d) * star Um := by
      rw [hs]
      calc Um * d * star Um * (Um * d * star Um) = Um * d * (star Um * Um) * d * star Um := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hUU, Matrix.mul_one, Matrix.mul_assoc Um d d]
    rw [hGG, Matrix.trace_mul_cycle, hUU, Matrix.one_mul, diagonal_mul_diagonal, trace_diagonal]
    simp [hev, RCLike.ofReal_real_eq_id, sq]
  rw [htr, htr2, hrk, ← Finset.sum_filter_ne_zero, Fintype.card_subtype]
  calc (∑ i ∈ Finset.univ.filter (fun i => ev i ≠ 0), ev i) ^ 2
      ≤ ((Finset.univ.filter (fun i => ev i ≠ 0)).card : ℝ) *
          ∑ i ∈ Finset.univ.filter (fun i => ev i ≠ 0), ev i ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ _ := by
      gcongr
      exact Finset.subset_univ _

section

variable {n : Nat} {A : Mat} {k t lam mu : Int}

theorem toR_mul (X Y : Mat) : toR n (mul n X Y) = toR n X * toR n Y := by
  ext i j
  simp only [toR, mul, Matrix.of_apply, Matrix.mul_apply, sumBelow_eq_fin]
  push_cast; rfl

theorem toR_transpose (X : Mat) : toR n (transpose X) = (toR n X)ᵀ := by
  ext i j; rfl

theorem traceDDt2_eq : (traceDDt2 n A : ℝ) =
    (Dr n A * (Dr n A)ᵀ * (Dr n A * (Dr n A)ᵀ)).trace := by
  rw [← toR_D, ← toR_transpose, ← toR_mul, ← toR_mul]
  unfold traceDDt2
  rw [sumBelow_eq_fin]
  push_cast
  rfl

/-- `tr(DDᵀ) = 2n(k − t)`. -/
theorem trace_DrDrT (h : IsDSRG n A k t lam mu) :
    (Dr n A * (Dr n A)ᵀ).trace = 2 * (n : ℝ) * ((k : ℝ) - t) := by
  have hrow : ∀ i : Fin n, (Dr n A * (Dr n A)ᵀ) i i = 2 * ((k : ℝ) - t) := by
    intro i
    have e : ∀ j : Fin n, Dr n A i j * Dr n A i j =
        toR n A i j + toR n A j i - 2 * (toR n A i j * toR n A j i) := by
      intro j
      rcases h.1 i i.isLt j j.isLt with h1 | h1 <;> rcases h.1 j j.isLt i i.isLt with h2 | h2 <;>
        norm_num [Dr, toR, h1, h2]
    have hk1 : ∑ j, toR n A i j = k := by
      have := congrFun (congrFun (toR_mul_Jr h) i) i
      simpa [Matrix.mul_apply, Jr] using this
    have hk2 : ∑ j, toR n A j i = k := by
      have := congrFun (congrFun (Jr_mul_toR h) i) i
      simpa [Matrix.mul_apply, Jr] using this
    have ht : ∑ j, toR n A i j * toR n A j i = t := by
      have := congrFun (congrFun (toR_sq h) i) i
      simpa [Matrix.mul_apply, Jr, toR, h.2.1 i i.isLt] using this
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, e, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hk1, hk2, ht]
    ring
  rw [Matrix.trace]
  simp only [Matrix.diag, hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

theorem trace_bound (h : IsDSRG n A k t lam mu) :
    (2 * (n : Int) * kappa k t) ^ 2 ≤ ((toQ n (D A)).rank : Int) * traceDDt2 n A := by
  have hG : (Dr n A * (Dr n A)ᵀ).IsHermitian := by
    have := Matrix.isHermitian_mul_conjTranspose_self (Dr n A)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have key := trace_sq_le_rank_mul _ hG
  rw [Matrix.rank_self_mul_transpose, trace_DrDrT h, ← traceDDt2_eq] at key
  rw [rank_toQ_eq_toR, toR_D]
  unfold kappa
  have : (((2 * (n : Int) * (k - t)) ^ 2 : Int) : ℝ) ≤
      ((((Dr n A).rank : Int) * traceDDt2 n A : Int) : ℝ) := by
    push_cast; linarith
  exact_mod_cast this

end

end DsrgRank
