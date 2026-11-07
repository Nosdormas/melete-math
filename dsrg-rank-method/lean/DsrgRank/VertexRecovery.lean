import DsrgRank.SchurComplement

set_option autoImplicit false

namespace DsrgRank

open Matrix

section

variable {n : Nat} {A : Mat} {k t mu : Int}

theorem Recover_cover (h : IsDSRG n A k t 0 mu) (x i j : Fin n) :
    ∑ w ∈ (nbhd n A x)ᶜ, A i w * A w j =
      t * delta i j + mu * (1 - delta i j - A i j) - ∑ z ∈ nbhd n A x, A i z * A z j := by
  have e := h.2.2.2.2 i i.isLt j j.isLt
  rw [sumBelow_eq_fin] at e
  have hsplit := Finset.sum_add_sum_compl (nbhd n A x) (fun l : Fin n => A i l * A l j)
  linarith

theorem Recover_out_degree (h : IsDSRG n A k t 0 mu) (x i : Fin n) :
    ∑ w ∈ (nbhd n A x)ᶜ, A i w = k - ∑ z ∈ nbhd n A x, A i z := by
  have e := h.2.2.1 i i.isLt
  rw [sumBelow_eq_fin] at e
  have hsplit := Finset.sum_add_sum_compl (nbhd n A x) (fun l : Fin n => A i l)
  linarith

theorem Recover_in_degree (h : IsDSRG n A k t 0 mu) (x j : Fin n) :
    ∑ w ∈ (nbhd n A x)ᶜ, A w j = k - ∑ z ∈ nbhd n A x, A z j := by
  have e := h.2.2.2.1 j j.isLt
  rw [sumBelow_eq_fin] at e
  have hsplit := Finset.sum_add_sum_compl (nbhd n A x) (fun l : Fin n => A l j)
  linarith

theorem Recover_no_path2 (h : IsDSRG n A k t 0 mu) {x i j l : Fin n} (hi : i ∈ nbhd n A x)
    (hj : j ∈ nbhd n A x) (hl : l ∈ nbhd n A x) (hix : i ≠ x) (hjx : j ≠ x) (hlx : l ≠ x)
    (hij : A i j = 1) (hjl : A j l = 1) : False := by
  rcases ClosedNbhd_arcs h hi hj hij with ⟨e, _⟩ | ⟨_, e⟩ | ⟨_, _, _, hxj0⟩
  · exact hix e
  · exact hjx e
  · rcases ClosedNbhd_arcs h hj hl hjl with ⟨e, _⟩ | ⟨_, e⟩ | ⟨hxj1, _, _, _⟩
    · exact hjx e
    · exact hlx e
    · rw [hxj0] at hxj1
      exact absurd hxj1 (by decide)

theorem Recover_inv_nilp {m : Type*} [Fintype m] [DecidableEq m] (E : Matrix m m ℝ) (hE : E * E = 0)
    {θ : ℝ} (hθ : θ ≠ 0) :
    (E - θ • (1 : Matrix m m ℝ)) * (-(θ⁻¹) • (1 : Matrix m m ℝ) - (θ⁻¹ ^ 2) • E) = 1 := by
  have h1 : -θ⁻¹ * θ = -1 := by
    field_simp
  have h2 : θ⁻¹ ^ 2 * θ = θ⁻¹ := by
    field_simp
  simp only [sub_mul, mul_sub, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, hE,
    smul_zero, smul_smul]
  rw [h1, h2, neg_one_smul, neg_smul]
  abel

theorem Recover_det_zero_of_rank_lt {N m : Nat} (M : Matrix (Fin N) (Fin N) ℝ) (r c : Fin m → Fin N)
    (hM : M.rank < m) : (M.submatrix r c).det = 0 := by
  by_contra hdet
  have hu : IsUnit (M.submatrix r c) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 := Matrix.rank_submatrix_le M r c
  rw [h1, Fintype.card_fin] at h2
  omega

theorem Recover_det16 (h : IsDSRG 48 A 9 5 0 2) (r c : Fin 16 → Fin 48) :
    ((toR 48 A - (1 : ℝ) • (1 : Matrix (Fin 48) (Fin 48) ℝ)).submatrix r c).det = 0 := by
  apply Recover_det_zero_of_rank_lt
  rw [Schur_rank48 h]
  norm_num

end

end DsrgRank
