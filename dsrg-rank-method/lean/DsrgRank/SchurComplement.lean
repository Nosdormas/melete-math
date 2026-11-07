import DsrgRank.ClosedNeighbourhood

set_option autoImplicit false

namespace DsrgRank

open Matrix

section

variable {n : Nat} {A : Mat} {k t mu : Int}

noncomputable def yhat (n : Nat) (A : Mat) (x : Fin n) (θ : ℝ) (mu : Int) : Fin n → ℝ :=
  fun j => (if j = x then 1 + θ / mu else 0) + (A j x : ℝ) / mu

theorem Schur_colx (h : IsDSRG n A k t 0 mu) (i x : Fin n) :
    ∑ j : Fin n, (A i j : ℝ) * A j x =
      (t : ℝ) * (if i = x then 1 else 0) + mu * (1 - (if i = x then 1 else 0) - A i x) := by
  have e := h.2.2.2.2 i i.isLt x x.isLt
  rw [sumBelow_eq_fin] at e
  have e' : ((∑ j : Fin n, A i j * A j x : ℤ) : ℝ) =
      ((t * delta i x + 0 * A i x + mu * (1 - delta i x - A i x) : ℤ) : ℝ) := by
    rw [e]
  push_cast at e'
  rw [e']
  by_cases hix : i = x
  · subst hix
    simp [delta]
  · have hv : (i : Nat) ≠ x := Fin.val_ne_iff.mpr hix
    simp [delta, hix, hv]

theorem Schur_yhat (h : IsDSRG n A k t 0 mu) (hμ : mu ≠ 0) {θ θ' : ℝ}
    (hr : IsRootPair t 0 mu θ θ') (x : Fin n) :
    (toR n A - θ • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ yhat n A x θ mu = fun _ => 1 := by
  have hμR : (mu : ℝ) ≠ 0 := by exact_mod_cast hμ
  have hθ2 : θ ^ 2 + (mu : ℝ) * θ = (t : ℝ) - mu := by
    obtain ⟨h1, h2⟩ := hr
    have h1' : θ' = -(mu : ℝ) - θ := by push_cast at h1; linarith
    rw [h1'] at h2
    nlinarith
  funext i
  rw [ClosedNbhd_rowEq]
  have hsum : ∑ j : Fin n, (A i j : ℝ) * yhat n A x θ mu j =
      (A i x : ℝ) * (1 + θ / mu) + (∑ j : Fin n, (A i j : ℝ) * A j x) / mu := by
    have e1 : ∀ j : Fin n, (A i j : ℝ) * yhat n A x θ mu j =
        (if j = x then (A i j : ℝ) * (1 + θ / mu) else 0) + (A i j : ℝ) * A j x / mu := by
      intro j
      unfold yhat
      by_cases hj : j = x
      · simp [hj]
        ring
      · simp [hj]
        ring
    rw [Finset.sum_congr rfl (fun j _ => e1 j), Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_div]
    simp
  rw [hsum, Schur_colx h i x]
  by_cases hix : i = x
  · subst hix
    have hxx : (A i i : ℝ) = 0 := by exact_mod_cast h.2.1 i i.isLt
    simp only [yhat, ite_true, hxx]
    field_simp
    linear_combination -hθ2
  · simp only [yhat, hix, ite_false]
    field_simp
    ring

theorem Schur_kernel_of_card {M : Matrix (Fin n) (Fin n) ℝ} (S : Finset (Fin n))
    (hS : M.rank < S.card) :
    ∃ u : Fin n → ℝ, u ≠ 0 ∧ (∀ i, i ∉ S → u i = 0) ∧ M *ᵥ u = 0 := by
  classical
  let ι : (S → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun z i => if hi : i ∈ S then z ⟨i, hi⟩ else 0
      map_add' := by
        intro a b
        funext i
        by_cases hi : i ∈ S <;> simp [hi]
      map_smul' := by
        intro c a
        funext i
        by_cases hi : i ∈ S <;> simp [hi] }
  have hι : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    funext ⟨i, hi⟩
    have := congrFun hz i
    simpa [ι, hi] using this
  by_contra hno
  push Not at hno
  have hinj : Function.Injective (M.mulVecLin ∘ₗ ι) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    by_contra hz0
    have hu : ι z ≠ 0 := by
      intro e
      exact hz0 (hι (by rw [e, map_zero]))
    have hsupp : ∀ i, i ∉ S → ι z i = 0 := by
      intro i hi
      show (if hi'' : i ∈ S then z ⟨i, hi''⟩ else 0) = 0
      simp [hi]
    have hM : M *ᵥ ι z = 0 := by
      have := hz
      rw [LinearMap.comp_apply, Matrix.mulVecLin_apply] at this
      exact this
    exact hno (ι z) hu hsupp hM
  have h1 : Module.finrank ℝ (LinearMap.range (M.mulVecLin ∘ₗ ι)) = S.card := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe]
  have h2 : LinearMap.range (M.mulVecLin ∘ₗ ι) ≤ LinearMap.range M.mulVecLin :=
    LinearMap.range_comp_le_range _ _
  have h3 := Submodule.finrank_mono h2
  rw [h1] at h3
  exact absurd hS (not_lt.mpr h3)

theorem Schur_kernel_vector {lam : Int} (h : IsDSRG n A k t lam mu) (hn : 0 < n)
    (hpos : 0 < disc t lam mu) (hμ : mu ≠ 0) {θ θ' : ℝ} (hr : IsRootPair t lam mu θ θ')
    (S : Finset (Fin n)) (hS : 1 + Module.finrank ℝ (eigA n A θ') < S.card) :
    ∃ u : Fin n → ℝ, u ≠ 0 ∧ (∀ i, i ∉ S → u i = 0) ∧
      (toR n A - θ • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u = 0 := by
  apply Schur_kernel_of_card S
  rw [rank_sub_root h hn hpos hμ hr]
  exact hS

/-- (48, 9, 5, 0, 2): `dim E_{−3} = 14`. -/
theorem Schur_g48 (h : IsDSRG 48 A 9 5 0 2) : Module.finrank ℝ (eigA 48 A (-3)) = 14 := by
  have hd : disc 5 0 2 = 16 := by decide
  have hc : Real.sqrt (disc 5 0 2 : ℝ) = 4 := by
    rw [hd]
    rw [show ((16 : ℤ) : ℝ) = (4 : ℝ) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hrR : rR 5 0 2 = 1 := by
    unfold rR
    rw [hc]
    norm_num
  have hsR : sR 5 0 2 = -3 := by
    unfold sR
    rw [hc]
    norm_num
  obtain ⟨_, _, hsum, htr⟩ := spectrum_counts h (by norm_num) (by rw [hd]; norm_num) (by norm_num)
  rw [hrR, hsR] at hsum htr
  generalize Module.finrank ℝ ↥(eigA 48 A 1) = F at hsum htr ⊢
  generalize Module.finrank ℝ ↥(eigA 48 A (-3)) = G at hsum htr ⊢
  have hFG : (F : ℝ) + G = 47 := by exact_mod_cast hsum
  have hG : (G : ℝ) = 14 := by push_cast at htr; linarith
  exact_mod_cast hG

/-- (48, 9, 5, 0, 2): `rank(A − I) = 15`. -/
theorem Schur_rank48 (h : IsDSRG 48 A 9 5 0 2) :
    (toR 48 A - (1 : ℝ) • (1 : Matrix (Fin 48) (Fin 48) ℝ)).rank = 15 := by
  have hr : IsRootPair 5 0 2 (1 : ℝ) (-3) := by
    unfold IsRootPair
    norm_num
  rw [rank_sub_root h (by norm_num) (by decide) (by norm_num) hr, Schur_g48 h]

theorem Schur_pair48 (h : IsDSRG 48 A 9 5 0 2) (x w w' : Fin 48) (hw : w ∉ nbhd 48 A x)
    (hw' : w' ∉ nbhd 48 A x) (hne : w ≠ w') :
    ∃ u : Fin 48 → ℝ, u ≠ 0 ∧ (∀ i, i ∉ insert w (insert w' (nbhd 48 A x)) → u i = 0) ∧
      (toR 48 A - (1 : ℝ) • (1 : Matrix (Fin 48) (Fin 48) ℝ)) *ᵥ u = 0 := by
  have hr : IsRootPair 5 0 2 (1 : ℝ) (-3) := by
    unfold IsRootPair
    norm_num
  apply Schur_kernel_vector h (by norm_num) (by decide) (by norm_num) hr
  have hc := ClosedNbhd_card h x
  have hc' : (nbhd 48 A x).card = 14 := by
    norm_num at hc
    exact_mod_cast hc
  have hw2 : w ∉ insert w' (nbhd 48 A x) := by
    rw [Finset.mem_insert]
    rintro (e | e)
    · exact hne e
    · exact hw e
  rw [Finset.card_insert_of_notMem hw2, Finset.card_insert_of_notMem hw', hc', Schur_g48 h]
  norm_num

end

end DsrgRank
