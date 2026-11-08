module

public import DsrgRank.Spectrum.Mat

/-!
Defines the real matrices S_r and D_r of the discriminant decomposition, proves their transposition,
trace and product identities, and proves disc_pos: under 0 < t < k < n - 1 the discriminant is
positive.
-/

@[expose] public section

set_option autoImplicit false

namespace DsrgRank

open Matrix

section

variable {n : Nat} {A : Mat} {k t lam mu : Int}

noncomputable def Sr (n : Nat) (A : Mat) (k lam mu : Int) : Matrix (Fin n) (Fin n) ℝ :=
  toR n A + (toR n A)ᵀ - aR lam mu • (1 : Matrix (Fin n) (Fin n) ℝ) - betaR n k lam mu • Jr n

def Dr (n : Nat) (A : Mat) : Matrix (Fin n) (Fin n) ℝ := toR n A - (toR n A)ᵀ

theorem Mp_eq_S_add_D : Mp n A k lam mu = Sr n A k lam mu + Dr n A := by
  unfold Mp Sr Dr; module

theorem Mp_transpose : (Mp n A k lam mu)ᵀ = Sr n A k lam mu - Dr n A := by
  unfold Mp Sr Dr
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, Jr_transpose]
  module

theorem Sr_transpose : (Sr n A k lam mu)ᵀ = Sr n A k lam mu := by
  unfold Sr
  simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_one, Jr_transpose, Matrix.transpose_transpose]
  module

theorem Dr_transpose : (Dr n A)ᵀ = -Dr n A := by
  unfold Dr; simp [Matrix.transpose_sub]

theorem trace_Dr : (Dr n A).trace = 0 := by
  simp [Dr, Matrix.trace_sub, Matrix.trace_transpose]

/-- `tr M' = −(2k + (n − 1)(λ − μ))`. -/
theorem trace_Mp (h : IsDSRG n A k t lam mu) (hn : 0 < n) :
    (Mp n A k lam mu).trace = -((2 * k + ((n : ℤ) - 1) * (lam - mu) : ℤ) : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Mp, Matrix.trace_sub, Matrix.trace_smul, trace_toR h, Matrix.trace_one,
    Fintype.card_fin, trace_Jr, smul_eq_mul]
  unfold betaR aR
  push_cast
  field_simp
  ring

theorem trace_Mp_of_disc_zero (h : IsDSRG n A k t lam mu) (hn : 0 < n) (h0 : disc t lam mu = 0) :
    (Mp n A k lam mu).trace = 0 := by
  have hsq := Mp_sq h hn
  rw [h0, Int.cast_zero, zero_smul] at hsq
  have hnil : IsNilpotent (Mp n A k lam mu) := ⟨2, by rw [pow_two, hsq]⟩
  exact (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero

theorem Sr_mul_Jr (h : IsDSRG n A k t lam mu) (hn : 0 < n) : Sr n A k lam mu * Jr n = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Sr, Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, toR_mul_Jr h,
    toRT_mul_Jr h, Jr_mul_Jr, smul_smul]
  match_scalars
  unfold betaR; field_simp; ring1

theorem Jr_mul_Sr (h : IsDSRG n A k t lam mu) (hn : 0 < n) : Jr n * Sr n A k lam mu = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Sr, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Jr_mul_toR h,
    Jr_mul_toRT h, Jr_mul_Jr, smul_smul]
  match_scalars
  unfold betaR; field_simp; ring1

theorem Dr_mul_Jr (h : IsDSRG n A k t lam mu) : Dr n A * Jr n = 0 := by
  simp [Dr, Matrix.sub_mul, toR_mul_Jr h, toRT_mul_Jr h]

theorem Jr_mul_Dr (h : IsDSRG n A k t lam mu) : Jr n * Dr n A = 0 := by
  simp [Dr, Matrix.mul_sub, Jr_mul_toR h, Jr_mul_toRT h]

theorem dot_self_nonneg {m : Nat} (v : Fin m → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem dot_sq_symm {m : Nat} (T : Matrix (Fin m) (Fin m) ℝ) (hT : Tᵀ = T) (x : Fin m → ℝ) :
    x ⬝ᵥ (T * T) *ᵥ x = (T *ᵥ x) ⬝ᵥ (T *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  congr 1
  conv_lhs => rw [← hT]
  exact Matrix.vecMul_transpose T x

theorem trace_Mp_of_disc_neg (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hneg : disc t lam mu < 0) :
    (Mp n A k lam mu).trace = 0 := by
  set S := Sr n A k lam mu with hSdef
  set D := Dr n A with hDdef
  set δ : ℝ := (disc t lam mu : ℝ) with hδ
  have hδneg : δ < 0 := by rw [hδ]; exact_mod_cast hneg
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsq : (S + D) * (S + D) = δ • Pi1 n := by rw [← Mp_eq_S_add_D]; exact Mp_sq h hn
  have hsqT : (S - D) * (S - D) = δ • Pi1 n := by
    rw [← Mp_transpose, ← Matrix.transpose_mul, Mp_sq h hn, Matrix.transpose_smul, Pi1_transpose]
  have e1 : S * S + S * D + D * S + D * D = δ • Pi1 n := by
    rw [← hsq]; simp only [Matrix.add_mul, Matrix.mul_add]; abel
  have e2 : S * S - S * D - D * S + D * D = δ • Pi1 n := by
    rw [← hsqT]; simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
  have hanti : D * S = -(S * D) := by
    have h2x : (2 : ℝ) • (S * D + D * S) = 0 := by
      have : (2 : ℝ) • (S * D + D * S) =
          (S * S + S * D + D * S + D * D) - (S * S - S * D - D * S + D * D) := by module
      rw [this, e1, e2, sub_self]
    have h2 : S * D + D * S = 0 := by
      have := congrArg (fun X => (1 / 2 : ℝ) • X) h2x
      simpa [smul_smul] using this
    exact eq_neg_of_add_eq_zero_right h2
  have hDD : D * D = δ • Pi1 n - S * S := by
    have h2x : (2 : ℝ) • (S * S + D * D) = (2 : ℝ) • (δ • Pi1 n) := by
      have : (2 : ℝ) • (S * S + D * D) =
          (S * S + S * D + D * S + D * D) + (S * S - S * D - D * S + D * D) := by module
      rw [this, e1, e2]; module
    have h2 : S * S + D * D = δ • Pi1 n := smul_right_injective _ two_ne_zero h2x
    rw [← h2]; abel
  have hSJ : S * Jr n = 0 := Sr_mul_Jr h hn
  have hJS : Jr n * S = 0 := Jr_mul_Sr h hn
  have hDJ : D * Jr n = 0 := Dr_mul_Jr h
  have hJD : Jr n * D = 0 := Jr_mul_Dr h
  set Q := -(D * D) + (1 / (n : ℝ)) • Jr n with hQ
  have hPiS : Pi1 n * S = S := by
    simp [Pi1, Matrix.sub_mul, hJS]
  have hSPi : S * Pi1 n = S := by
    simp [Pi1, Matrix.mul_sub, hSJ]
  have hQ' : Q = S * S - δ • Pi1 n + (1 / (n : ℝ)) • Jr n := by rw [hQ, hDD]; abel
  have hJx : ∀ x : Fin n → ℝ, Jr n *ᵥ x = fun _ => ∑ i, x i := by
    intro x; ext i; simp [Jr, Matrix.mulVec, dotProduct]
  have hker : ∀ x, Q *ᵥ x = 0 → x = 0 := by
    intro x hx
    have hq : x ⬝ᵥ Q *ᵥ x = 0 := by rw [hx, dotProduct_zero]
    have hSsym : Sᵀ = S := Sr_transpose
    have hPisym : (Pi1 n)ᵀ = Pi1 n := Pi1_transpose
    have hform : x ⬝ᵥ Q *ᵥ x = (S *ᵥ x) ⬝ᵥ (S *ᵥ x) + (-δ) * ((Pi1 n *ᵥ x) ⬝ᵥ (Pi1 n *ᵥ x)) +
        (1 / (n : ℝ)) * (∑ i, x i) ^ 2 := by
      rw [hQ', Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        dotProduct_add, dotProduct_sub, dotProduct_smul, dotProduct_smul,
        dot_sq_symm S hSsym x]
      conv_lhs => rw [← Pi1_mul_Pi1 hn]
      rw [dot_sq_symm _ hPisym x, hJx]
      simp only [smul_eq_mul, dotProduct, ← Finset.sum_mul]
      ring
    rw [hform] at hq
    have h1 := dot_self_nonneg (S *ᵥ x)
    have h2 := dot_self_nonneg (Pi1 n *ᵥ x)
    have h3 : 0 ≤ (1 / (n : ℝ)) * (∑ i, x i) ^ 2 := by positivity
    have hP0 : (Pi1 n *ᵥ x) ⬝ᵥ (Pi1 n *ᵥ x) = 0 := by nlinarith
    have hs0 : (∑ i, x i) = 0 := by
      have h4 : (1 / (n : ℝ)) * (∑ i, x i) ^ 2 = 0 := by nlinarith
      have hpos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
      have h5 := (mul_eq_zero.mp h4).resolve_left hpos.ne'
      exact pow_eq_zero_iff two_ne_zero |>.mp h5
    have hPx : Pi1 n *ᵥ x = 0 := dotProduct_self_eq_zero.mp hP0
    have hx' : x = Pi1 n *ᵥ x + (1 / (n : ℝ)) • (Jr n *ᵥ x) := by
      rw [Pi1, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]; abel
    rw [hx', hPx, hJx, hs0]
    ext i; simp
  have hinj : Function.Injective Q.mulVec := by
    intro x y hxy
    have : Q *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hker _ this)
  have hU : IsUnit Q := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hU
  set W := Q⁻¹ with hW
  have hWQ : W * Q = 1 := Matrix.nonsing_inv_mul Q hdet
  have hQW : Q * W = 1 := Matrix.mul_nonsing_inv Q hdet
  have hcomm : ∀ X : Matrix (Fin n) (Fin n) ℝ, X * Q = Q * X → X * W = W * X := by
    intro X hX
    calc X * W = (W * Q) * X * W := by rw [hWQ, Matrix.one_mul]
      _ = W * (X * Q) * W := by rw [hX]; simp only [Matrix.mul_assoc]
      _ = W * X * (Q * W) := by simp only [Matrix.mul_assoc]
      _ = W * X := by rw [hQW, Matrix.mul_one]
  have hDQ : D * Q = Q * D := by
    rw [hQ]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_smul, Matrix.smul_mul, hDJ, hJD, Matrix.mul_assoc]
  have hDW := hcomm D hDQ
  have hDW' : ∀ X : Matrix (Fin n) (Fin n) ℝ, D * (W * X) = W * (D * X) := fun X => by
    rw [← Matrix.mul_assoc, hDW, Matrix.mul_assoc]
  have hQJ : Q * Jr n = Jr n := by
    rw [hQ]; simp only [Matrix.add_mul, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_assoc, hDJ,
      Matrix.mul_zero, neg_zero, zero_add, Jr_mul_Jr, smul_smul]
    rw [one_div, inv_mul_cancel₀ hn', one_smul]
  have hWJ : W * Jr n = Jr n := by
    calc W * Jr n = W * (Q * Jr n) := by rw [hQJ]
      _ = Jr n := by rw [← Matrix.mul_assoc, hWQ, Matrix.one_mul]
  have hSeq : S = -(S * W * D * D) := by
    calc S = S * (W * Q) := by rw [hWQ, Matrix.mul_one]
      _ = -(S * W * D * D) + (1 / (n : ℝ)) • (S * (W * Jr n)) := by
        rw [hQ]; simp only [Matrix.mul_add, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_assoc]
      _ = -(S * W * D * D) := by rw [hWJ, hSJ, smul_zero, add_zero]
  have htrS : S.trace = 0 := by
    have h1 : S.trace = -(S * W * D * D).trace := by
      conv_lhs => rw [hSeq]
      rw [Matrix.trace_neg]
    have h2 : (S * W * D * D).trace = (D * S * W * D).trace := by
      rw [Matrix.trace_mul_comm (S * W * D) D]; simp only [Matrix.mul_assoc]
    have h3 : D * S * W * D = -(S * W * D * D) := by
      rw [hanti]; simp only [Matrix.neg_mul, Matrix.mul_assoc, hDW']
    have h4 := h1
    rw [h2, h3, Matrix.trace_neg, neg_neg] at h4
    linarith
  rw [Mp_eq_S_add_D, Matrix.trace_add, htrS, trace_Dr, add_zero]

theorem trace_Mp_ne_zero (h : IsDSRG n A k t lam mu) (ht : 0 < t) (htk : t < k)
    (hkn : k < (n : Int) - 1) : (Mp n A k lam mu).trace ≠ 0 := by
  have hn : 0 < n := by omega
  intro h0
  rw [trace_Mp h hn, neg_eq_zero] at h0
  have hX : 2 * k + ((n : ℤ) - 1) * (lam - mu) = 0 := by exact_mod_cast h0
  have hk := k_sq h hn
  have hkZ : k ^ 2 = t + lam * k + mu * ((n : ℤ) - 1 - k) := by exact_mod_cast hk
  -- λ − μ = −1
  have ha : lam - mu = -1 := by
    rcases lt_trichotomy (lam - mu) (-1) with hlt | heq | hgt
    · nlinarith
    · exact heq
    · nlinarith
  have hn2 : (n : ℤ) - 1 = 2 * k := by nlinarith
  have htm : t = k * (k + 1 - 2 * mu) := by
    have hl : lam = mu - 1 := by omega
    subst hl
    nlinarith
  rcases le_or_gt (k + 1 - 2 * mu) 0 with hm | hm
  · nlinarith
  · nlinarith

end

theorem disc_pos {n : Nat} {A : Mat} {k t lam mu : Int} (h : IsDSRG n A k t lam mu)
    (ht : 0 < t) (htk : t < k) (hkn : k < (n : Int) - 1) : 0 < disc t lam mu := by
  have hn : 0 < n := by omega
  by_contra hle
  replace hle := not_lt.mp hle
  rcases hle.lt_or_eq with hneg | h0
  · exact trace_Mp_ne_zero h ht htk hkn (trace_Mp_of_disc_neg h hn hneg)
  · exact trace_Mp_ne_zero h ht htk hkn (trace_Mp_of_disc_zero h hn h0)

end DsrgRank
