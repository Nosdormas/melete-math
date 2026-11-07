import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import DsrgRank.Spectral

set_option autoImplicit false

namespace DsrgRank

open Matrix

noncomputable def Kth (n : Nat) (A : Mat) (k : Int) (θ : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (n : ℝ) • (toR n A - θ • (1 : Matrix (Fin n) (Fin n) ℝ)) - ((k : ℝ) - θ) • Jr n

section

variable {n : Nat} {A : Mat} {k t lam mu : Int} {θ θ' : ℝ}

theorem KerFrame_subJ (h : IsDSRG n A k t lam mu) (c : ℝ) :
    (toR n A - c • (1 : Matrix (Fin n) (Fin n) ℝ)) * Jr n = ((k : ℝ) - c) • Jr n := by
  rw [Matrix.sub_mul, toR_mul_Jr h, Matrix.smul_mul, Matrix.one_mul, sub_smul]

theorem KerFrame_Jsub (h : IsDSRG n A k t lam mu) (c : ℝ) :
    Jr n * (toR n A - c • (1 : Matrix (Fin n) (Fin n) ℝ)) = ((k : ℝ) - c) • Jr n := by
  rw [Matrix.mul_sub, Jr_mul_toR h, Matrix.mul_smul, Matrix.mul_one, sub_smul]

theorem KerFrame_left_null (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hr : IsRootPair t lam mu θ θ') :
    (toR n A - θ' • (1 : Matrix (Fin n) (Fin n) ℝ)) * Kth n A k θ = 0 := by
  unfold Kth
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, sub_mul_sub_eq h hr, KerFrame_subJ h,
    smul_smul, smul_smul, ← sub_smul]
  have e : (n : ℝ) * mu - ((k : ℝ) - θ) * ((k : ℝ) - θ') = 0 := by
    rw [k_sub_mul_k_sub h hn hr]; ring
  rw [e, zero_smul]

theorem KerFrame_right_null (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hr : IsRootPair t lam mu θ θ') :
    Kth n A k θ * (toR n A - θ' • (1 : Matrix (Fin n) (Fin n) ℝ)) = 0 := by
  unfold Kth
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, sub_mul_sub_eq h hr.symm, KerFrame_Jsub h,
    smul_smul, smul_smul, ← sub_smul]
  have e : (n : ℝ) * mu - ((k : ℝ) - θ) * ((k : ℝ) - θ') = 0 := by
    rw [k_sub_mul_k_sub h hn hr]; ring
  rw [e, zero_smul]

theorem KerFrame_A_mul_K (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hr : IsRootPair t lam mu θ θ') :
    toR n A * Kth n A k θ = θ' • Kth n A k θ := by
  have e := KerFrame_left_null h hn hr
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_zero] at e
  exact e

theorem KerFrame_K_mul_A (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hr : IsRootPair t lam mu θ θ') :
    Kth n A k θ * toR n A = θ' • Kth n A k θ := by
  have e := KerFrame_right_null h hn hr
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, sub_eq_zero] at e
  exact e

theorem KerFrame_K_mul_J (h : IsDSRG n A k t lam mu) : Kth n A k θ * Jr n = 0 := by
  unfold Kth
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, KerFrame_subJ h, Jr_mul_Jr, smul_smul,
    smul_smul, show (n : ℝ) * ((k : ℝ) - θ) = ((k : ℝ) - θ) * n by ring, sub_self]

theorem KerFrame_J_mul_K (h : IsDSRG n A k t lam mu) : Jr n * Kth n A k θ = 0 := by
  unfold Kth
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, KerFrame_Jsub h, Jr_mul_Jr, smul_smul,
    smul_smul, show (n : ℝ) * ((k : ℝ) - θ) = ((k : ℝ) - θ) * n by ring, sub_self]

theorem KerFrame_K_sq (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hr : IsRootPair t lam mu θ θ') :
    Kth n A k θ * Kth n A k θ = ((n : ℝ) * (θ' - θ)) • Kth n A k θ := by
  have hK : Kth n A k θ * Kth n A k θ =
      Kth n A k θ * ((n : ℝ) • (toR n A - θ • (1 : Matrix (Fin n) (Fin n) ℝ)) -
        ((k : ℝ) - θ) • Jr n) := rfl
  rw [hK, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, KerFrame_K_mul_J h, smul_zero, sub_zero,
    Matrix.mul_sub, KerFrame_K_mul_A h hn hr, Matrix.mul_smul, Matrix.mul_one, ← sub_smul, smul_smul]

theorem KerFrame_eigvec (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hr : IsRootPair t lam mu θ θ')
    (z : Fin n → ℝ) :
    toR n A *ᵥ (Kth n A k θ *ᵥ z) = θ' • (Kth n A k θ *ᵥ z) := by
  rw [Matrix.mulVec_mulVec, KerFrame_A_mul_K h hn hr, Matrix.smul_mulVec]

theorem KerFrame_left_eigvec (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hr : IsRootPair t lam mu θ θ')
    (u : Fin n → ℝ) :
    (u ᵥ* Kth n A k θ) ᵥ* toR n A = θ' • (u ᵥ* Kth n A k θ) := by
  rw [Matrix.vecMul_vecMul, KerFrame_K_mul_A h hn hr, Matrix.vecMul_smul]

theorem KerFrame_frame_kernel (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hr : IsRootPair t lam mu θ θ')
    (F : Finset (Fin n)) (z : Fin n → ℝ) (hz : ∀ i ∈ F, (Kth n A k θ *ᵥ z) i = 0) :
    ∀ i ∈ F, (toR n A *ᵥ (Kth n A k θ *ᵥ z)) i = 0 := by
  intro i hi
  rw [KerFrame_eigvec h hn hr z, Pi.smul_apply, hz i hi, smul_zero]

theorem KerFrame_frame_singular_out (h : IsDSRG n A k t lam mu) (hn : 0 < n)
    (hr : IsRootPair t lam mu θ θ') (hθ' : θ' ≠ 0) (x : Fin n) (F : Finset (Fin n)) (hx : x ∈ F)
    (hF : ∀ j : Fin n, A x j = 1 → j ∈ F) :
    ((Kth n A k θ).submatrix (fun i : F => (i : Fin n)) (fun i : F => (i : Fin n))).det = 0 := by
  rw [← Matrix.exists_vecMul_eq_zero_iff]
  have hoff : ∀ i : Fin n, i ∉ F →
      (toR n A - θ' • (1 : Matrix (Fin n) (Fin n) ℝ)) x i = 0 := by
    intro i hi
    have hxi : x ≠ i := fun e => hi (e ▸ hx)
    rcases h.1 x x.isLt i i.isLt with h0 | h1
    · simp [toR, h0, Matrix.one_apply_ne hxi]
    · exact absurd (hF i h1) hi
  refine ⟨fun i => (toR n A - θ' • (1 : Matrix (Fin n) (Fin n) ℝ)) x i, ?_, ?_⟩
  · intro hv
    have e := congrFun hv ⟨x, hx⟩
    simp [toR, h.2.1 x x.isLt] at e
    exact hθ' e
  · funext j
    have hnull := congrFun (congrFun (KerFrame_left_null h hn hr) x) j
    rw [Matrix.mul_apply] at hnull
    simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, Pi.zero_apply]
    rw [Finset.sum_coe_sort F (fun i => (toR n A - θ' • (1 : Matrix (Fin n) (Fin n) ℝ)) x i *
      Kth n A k θ i j)]
    rw [Finset.sum_subset (Finset.subset_univ F) (fun i _ hi => by rw [hoff i hi, zero_mul])]
    exact hnull

theorem KerFrame_frame_singular_in (h : IsDSRG n A k t lam mu) (hn : 0 < n)
    (hr : IsRootPair t lam mu θ θ') (hθ' : θ' ≠ 0) (x : Fin n) (F : Finset (Fin n)) (hx : x ∈ F)
    (hF : ∀ i : Fin n, A i x = 1 → i ∈ F) :
    ((Kth n A k θ).submatrix (fun i : F => (i : Fin n)) (fun i : F => (i : Fin n))).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  have hoff : ∀ i : Fin n, i ∉ F →
      (toR n A - θ' • (1 : Matrix (Fin n) (Fin n) ℝ)) i x = 0 := by
    intro i hi
    have hix : i ≠ x := fun e => hi (e ▸ hx)
    rcases h.1 i i.isLt x x.isLt with h0 | h1
    · simp [toR, h0, Matrix.one_apply_ne hix]
    · exact absurd (hF i h1) hi
  refine ⟨fun i => (toR n A - θ' • (1 : Matrix (Fin n) (Fin n) ℝ)) i x, ?_, ?_⟩
  · intro hv
    have e := congrFun hv ⟨x, hx⟩
    simp [toR, h.2.1 x x.isLt] at e
    exact hθ' e
  · funext i
    have hnull := congrFun (congrFun (KerFrame_right_null h hn hr) i) x
    rw [Matrix.mul_apply] at hnull
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.zero_apply]
    rw [Finset.sum_coe_sort F (fun j => Kth n A k θ i j *
      (toR n A - θ' • (1 : Matrix (Fin n) (Fin n) ℝ)) j x)]
    rw [Finset.sum_subset (Finset.subset_univ F) (fun j _ hj => by rw [hoff j hj, mul_zero])]
    exact hnull

theorem KerFrame_frame_singular_out_k (h : IsDSRG n A k t lam mu) (hn : 0 < n)
    (hr : IsRootPair t lam mu θ θ') (x j : Fin n) (hxj : A x j = 1) (F : Finset (Fin n))
    (hx : x ∈ F) (hF : ∀ j : Fin n, A x j = 1 → j ∈ F) :
    ((Kth n A k θ).submatrix (fun i : F => (i : Fin n)) (fun i : F => (i : Fin n))).det = 0 := by
  rw [← Matrix.exists_vecMul_eq_zero_iff]
  have hoff : ∀ i : Fin n, i ∉ F →
      (toR n A - θ' • (1 : Matrix (Fin n) (Fin n) ℝ)) x i = 0 := by
    intro i hi
    have hxi : x ≠ i := fun e => hi (e ▸ hx)
    rcases h.1 x x.isLt i i.isLt with h0 | h1
    · simp [toR, h0, Matrix.one_apply_ne hxi]
    · exact absurd (hF i h1) hi
  have hxj' : x ≠ j := by
    intro e
    rw [← e, h.2.1 x x.isLt] at hxj
    exact absurd hxj (by decide)
  refine ⟨fun i => (toR n A - θ' • (1 : Matrix (Fin n) (Fin n) ℝ)) x i, ?_, ?_⟩
  · intro hv
    have e := congrFun hv ⟨j, hF j hxj⟩
    simp [toR, hxj, Matrix.one_apply_ne hxj'] at e
  · funext j
    have hnull := congrFun (congrFun (KerFrame_left_null h hn hr) x) j
    rw [Matrix.mul_apply] at hnull
    simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, Pi.zero_apply]
    rw [Finset.sum_coe_sort F (fun i => (toR n A - θ' • (1 : Matrix (Fin n) (Fin n) ℝ)) x i *
      Kth n A k θ i j)]
    rw [Finset.sum_subset (Finset.subset_univ F) (fun i _ hi => by rw [hoff i hi, zero_mul])]
    exact hnull

theorem KerFrame_frame_singular_in_k (h : IsDSRG n A k t lam mu) (hn : 0 < n)
    (hr : IsRootPair t lam mu θ θ') (x j : Fin n) (hjx : A j x = 1) (F : Finset (Fin n))
    (hx : x ∈ F) (hF : ∀ i : Fin n, A i x = 1 → i ∈ F) :
    ((Kth n A k θ).submatrix (fun i : F => (i : Fin n)) (fun i : F => (i : Fin n))).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  have hoff : ∀ i : Fin n, i ∉ F →
      (toR n A - θ' • (1 : Matrix (Fin n) (Fin n) ℝ)) i x = 0 := by
    intro i hi
    have hix : i ≠ x := fun e => hi (e ▸ hx)
    rcases h.1 i i.isLt x x.isLt with h0 | h1
    · simp [toR, h0, Matrix.one_apply_ne hix]
    · exact absurd (hF i h1) hi
  have hjx' : j ≠ x := by
    intro e
    rw [e, h.2.1 x x.isLt] at hjx
    exact absurd hjx (by decide)
  refine ⟨fun i => (toR n A - θ' • (1 : Matrix (Fin n) (Fin n) ℝ)) i x, ?_, ?_⟩
  · intro hv
    have e := congrFun hv ⟨j, hF j hjx⟩
    simp [toR, hjx, Matrix.one_apply_ne hjx'] at e
  · funext i
    have hnull := congrFun (congrFun (KerFrame_right_null h hn hr) i) x
    rw [Matrix.mul_apply] at hnull
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.zero_apply]
    rw [Finset.sum_coe_sort F (fun j => Kth n A k θ i j *
      (toR n A - θ' • (1 : Matrix (Fin n) (Fin n) ℝ)) j x)]
    rw [Finset.sum_subset (Finset.subset_univ F) (fun j _ hj => by rw [hoff j hj, mul_zero])]
    exact hnull

theorem KerFrame_range (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hr : IsRootPair t lam mu θ θ')
    (hne : θ ≠ θ') (hk : (k : ℝ) ≠ θ') :
    LinearMap.range (Kth n A k θ).mulVecLin = eigA n A θ' := by
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    rw [mem_eigA, Matrix.mulVecLin_apply]
    exact KerFrame_eigvec h hn hr z
  · intro x hx
    rw [mem_eigA] at hx
    have hJ := Jr_mulVec_of_eig h hx hk
    have hc : (n : ℝ) * (θ' - θ) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hn.ne') (sub_ne_zero.mpr (Ne.symm hne))
    have hK : Kth n A k θ *ᵥ x = ((n : ℝ) * (θ' - θ)) • x := by
      unfold Kth
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hx, hJ, smul_zero,
        sub_zero]
      module
    refine ⟨((n : ℝ) * (θ' - θ))⁻¹ • x, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_smul, hK, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem KerFrame_rank (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hr : IsRootPair t lam mu θ θ')
    (hne : θ ≠ θ') (hk : (k : ℝ) ≠ θ') :
    (Kth n A k θ).rank = Module.finrank ℝ (eigA n A θ') := by
  rw [← KerFrame_range h hn hr hne hk]; rfl

theorem KerFrame_rank_duval (h : IsDSRG n A k t lam mu) (ht : 0 < t) (htk : t < k)
    (hkn : k < (n : Int) - 1) (hr : IsRootPair t lam mu θ θ') :
    (Kth n A k θ).rank = Module.finrank ℝ (eigA n A θ') ∧
    (Kth n A k θ).rank + 1 = (toR n A - θ • (1 : Matrix (Fin n) (Fin n) ℝ)).rank := by
  have hn : 0 < n := by omega
  have hpos := disc_pos h ht htk hkn
  have hμ := (mu_pos h ht htk hkn).ne'
  have hk := (k_ne_root h hn hμ hr).2
  have hne : θ ≠ θ' := by
    have hc := cR_pos hpos
    have hrs := rR_sub_sR (t := t) (lam := lam) (mu := mu)
    rcases root_cases hpos hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> intro e <;> linarith
  have hK := KerFrame_rank h hn hr hne hk
  refine ⟨hK, ?_⟩
  rw [hK, rank_sub_root h hn hpos hμ hr]; ring

end

end DsrgRank
