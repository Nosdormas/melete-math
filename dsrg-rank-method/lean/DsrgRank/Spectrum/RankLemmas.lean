module

public import Mathlib.LinearAlgebra.Trace
public import DsrgRank.Spectrum.Disc

/-!
Proves rank lemmas for the spectral lemma: facts about block matrices, equality of the ranks of
rational and real forms, the trace of an idempotent equals its rank, and rank_D_parts, which gives
the multiplicities f and g of the two roots with their equations.
-/

@[expose] public section

set_option autoImplicit false

namespace DsrgRank

open Matrix

theorem rank_fromBlocks_one {K : Type*} [Field K] (r s : Nat) :
    (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 0 (0 : Matrix (Fin s) (Fin s) K)).rank
      = r := by
  classical
  rw [← Matrix.diagonal_one, ← Matrix.diagonal_zero, Matrix.fromBlocks_diagonal,
    Matrix.rank_diagonal, Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  simp

theorem rank_toQ_eq_toR {n : Nat} (M : Mat) : (toQ n M).rank = (toR n M).rank := by
  classical
  obtain ⟨V, U, e, hV, hU, hVMU⟩ := Matrix.exists_rank_normal_form (toQ n M)
  set f := Rat.castHom ℝ
  have hmap : (toQ n M).map f = toR n M := by ext i j; simp [toQ, toR, f]
  have h1 : V.map f * toR n M * U.map f =
      ((Matrix.fromBlocks 1 0 0 0).submatrix e e).map f := by
    rw [← hmap, ← Matrix.map_mul, ← Matrix.map_mul, hVMU]
  have hV' : IsUnit (V.map f).det := by
    have e : (V.map f).det = f V.det := (RingHom.map_det f V).symm
    rw [e]; exact ((Matrix.isUnit_iff_isUnit_det V).mp hV).map f
  have hU' : IsUnit (U.map f).det := by
    have e : (U.map f).det = f U.det := (RingHom.map_det f U).symm
    rw [e]; exact ((Matrix.isUnit_iff_isUnit_det U).mp hU).map f
  have r1 : (toR n M).rank = (((Matrix.fromBlocks 1 0 0 0).submatrix e e).map f).rank := by
    rw [← h1, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hU',
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hV']
  rw [r1, ← Matrix.submatrix_map, Matrix.rank_submatrix, Matrix.fromBlocks_map,
    Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_zero _ (map_zero f),
    Matrix.map_zero _ (map_zero f), Matrix.map_zero _ (map_zero f), rank_fromBlocks_one]

theorem trace_eq_rank_of_idem {n : Nat} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P * P = P) :
    P.trace = (P.rank : ℝ) := by
  have hidem : IsIdempotentElem (Matrix.toLin' P) := by
    show Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
  have := (LinearMap.IsIdempotentElem.isProj_range _ hidem).trace
  rw [Matrix.trace_toLin'_eq] at this
  rw [this]
  rfl

open Module in

theorem rank_add_two_rank_le {m : Nat} (Dm M P Pi : Matrix (Fin m) (Fin m) ℝ) (c : ℝ)
    (v : Fin m → ℝ) (hv : v ≠ 0) (hDv : Dm *ᵥ v = 0) (hPiv : Pi *ᵥ v = 0)
    (hPi : Pi * Pi = Pi) (hPiP : Pi * P = P) (hPiPt : Pi * Pᵀ = Pᵀ)
    (hMP : M * P = c • P) (hMtPt : Mᵀ * Pᵀ = c • Pᵀ)
    (hD : ∀ x, M *ᵥ x = c • x → Mᵀ *ᵥ x = c • x → Dm *ᵥ x = 0) :
    Dm.rank + 2 * P.rank + 1 ≤ m + Pi.rank := by
  classical
  set U := LinearMap.range P.mulVecLin with hUdef
  set U' := LinearMap.range Pᵀ.mulVecLin with hU'def
  set W := LinearMap.range Pi.mulVecLin with hWdef
  set K := LinearMap.ker Dm.mulVecLin with hKdef
  have hUW : U ≤ W := by
    rintro x ⟨a, rfl⟩
    exact ⟨P *ᵥ a, by simp [Matrix.mulVec_mulVec, hPiP]⟩
  have hU'W : U' ≤ W := by
    rintro x ⟨a, rfl⟩
    exact ⟨Pᵀ *ᵥ a, by simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hPiPt]⟩
  have hfix : ∀ x ∈ W, Pi *ᵥ x = x := by
    rintro x ⟨a, rfl⟩; simp [Matrix.mulVec_mulVec, hPi]
  have hIK : U ⊓ U' ≤ K := by
    rintro x ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    simp only [Matrix.mulVecLin_apply] at ha hb
    have h1 : M *ᵥ x = c • x := by
      rw [← ha, Matrix.mulVec_mulVec, hMP, Matrix.smul_mulVec]
    have h2 : Mᵀ *ᵥ x = c • x := by
      rw [← hb, Matrix.mulVec_mulVec, hMtPt, Matrix.smul_mulVec]
    show Dm.mulVecLin x = 0
    simpa using hD x h1 h2
  have hvK : (ℝ ∙ v) ≤ K := by
    rw [Submodule.span_singleton_le_iff_mem]; simpa [hKdef] using hDv
  have hdisj : (U ⊓ U') ⊓ (ℝ ∙ v) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hxU, _⟩, hxv⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hxv
    have := hfix _ (hUW hxU)
    rw [Matrix.mulVec_smul, hPiv, smul_zero] at this
    rw [Submodule.mem_bot]; exact this.symm
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq U U'
  have e2 := Submodule.finrank_sup_add_finrank_inf_eq (U ⊓ U') (ℝ ∙ v)
  rw [hdisj, finrank_bot, finrank_span_singleton hv] at e2
  have m1 : finrank ℝ ↥(U ⊔ U') ≤ finrank ℝ W := Submodule.finrank_mono (sup_le hUW hU'W)
  have m2 : finrank ℝ ↥((U ⊓ U') ⊔ (ℝ ∙ v)) ≤ finrank ℝ K :=
    Submodule.finrank_mono (sup_le hIK hvK)
  have e3 : finrank ℝ (LinearMap.range Dm.mulVecLin) + finrank ℝ K = m := by
    rw [hKdef, LinearMap.finrank_range_add_finrank_ker, Module.finrank_fin_fun]
  have rP : P.rank = finrank ℝ U := rfl
  have rPt : Pᵀ.rank = finrank ℝ U' := rfl
  have rPi : Pi.rank = finrank ℝ W := rfl
  have rD : Dm.rank = finrank ℝ (LinearMap.range Dm.mulVecLin) := rfl
  rw [Matrix.rank_transpose] at rPt
  omega

section

variable {n : Nat} {A : Mat} {k t lam mu : Int}

/-- `c = √Δ`. -/
noncomputable def cR (t lam mu : Int) : ℝ := Real.sqrt (disc t lam mu)

/-- `P₊ = Π/2 + M'/(2c)`. -/
noncomputable def Pp (n : Nat) (A : Mat) (k t lam mu : Int) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • Pi1 n + (1 / (2 * cR t lam mu)) • Mp n A k lam mu

/-- `P₋ = Π/2 − M'/(2c)`. -/
noncomputable def Pm (n : Nat) (A : Mat) (k t lam mu : Int) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • Pi1 n - (1 / (2 * cR t lam mu)) • Mp n A k lam mu

theorem cR_pos (hpos : 0 < disc t lam mu) : 0 < cR t lam mu :=
  Real.sqrt_pos.mpr (by exact_mod_cast hpos)

theorem cR_sq (hpos : 0 < disc t lam mu) : cR t lam mu * cR t lam mu = (disc t lam mu : ℝ) :=
  Real.mul_self_sqrt (by exact_mod_cast hpos.le)

theorem toR_D : toR n (D A) = Dr n A := by
  ext i j; simp only [toR, Dr, D, N, U, Matrix.of_apply, Matrix.sub_apply, Matrix.transpose_apply]
  push_cast; ring

theorem Pi1_mul_Mp (h : IsDSRG n A k t lam mu) (hn : 0 < n) :
    Pi1 n * Mp n A k lam mu = Mp n A k lam mu := by
  simp [Pi1, Matrix.sub_mul, Jr_mul_Mp h hn]

theorem Mp_mul_Pi1 (h : IsDSRG n A k t lam mu) (hn : 0 < n) :
    Mp n A k lam mu * Pi1 n = Mp n A k lam mu := by
  simp [Pi1, Matrix.mul_sub, Mp_mul_Jr h hn]

theorem Pi1_mul_MpT (h : IsDSRG n A k t lam mu) (hn : 0 < n) :
    Pi1 n * (Mp n A k lam mu)ᵀ = (Mp n A k lam mu)ᵀ := by
  have := congrArg Matrix.transpose (Mp_mul_Pi1 h hn)
  rwa [Matrix.transpose_mul, Pi1_transpose] at this

theorem trace_Pi1 (hn : 0 < n) : (Pi1 n).trace = (n : ℝ) - 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [Pi1, Matrix.trace_sub, Matrix.trace_smul, trace_Jr, hn']

/-- `M'P± = ±cP±`, `P±M' = ±cP±`, `P±² = P±`, `ΠP± = P±`. -/
theorem Pp_props (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hpos : 0 < disc t lam mu) :
    Mp n A k lam mu * Pp n A k t lam mu = cR t lam mu • Pp n A k t lam mu ∧
    Pp n A k t lam mu * Mp n A k lam mu = cR t lam mu • Pp n A k t lam mu ∧
    Pp n A k t lam mu * Pp n A k t lam mu = Pp n A k t lam mu ∧
    Pi1 n * Pp n A k t lam mu = Pp n A k t lam mu ∧
    Mp n A k lam mu * Pm n A k t lam mu = (-cR t lam mu) • Pm n A k t lam mu ∧
    Pm n A k t lam mu * Mp n A k lam mu = (-cR t lam mu) • Pm n A k t lam mu ∧
    Pm n A k t lam mu * Pm n A k t lam mu = Pm n A k t lam mu ∧
    Pi1 n * Pm n A k t lam mu = Pm n A k t lam mu := by
  have hc := cR_pos hpos
  have hc2 := cR_sq hpos
  have hc' : cR t lam mu ≠ 0 := hc.ne'
  have hsq := Mp_sq h hn
  have hPM := Pi1_mul_Mp h hn
  have hMP := Mp_mul_Pi1 h hn
  have hPP := Pi1_mul_Pi1 hn
  rw [← hc2] at hsq
  unfold Pp Pm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, hsq, hPM, hMP, hPP, smul_smul, smul_add, smul_sub] <;>
  match_scalars <;> field_simp <;> ring1

theorem Pi1_mul_Jr (hn : 0 < n) : Pi1 n * Jr n = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Pi1, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Jr_mul_Jr, smul_smul]
  rw [one_div, inv_mul_cancel₀ hn', one_smul, sub_self]

theorem mulVec_ones_of_mul_Jr (hn : 0 < n) (X : Matrix (Fin n) (Fin n) ℝ) (hX : X * Jr n = 0) :
    X *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  ext i
  have := congrFun (congrFun hX i) ⟨0, hn⟩
  simpa [Matrix.mul_apply, Jr, Matrix.mulVec, dotProduct] using this

theorem Dr_mulVec_of_eigen (c : ℝ) (x : Fin n → ℝ) (h1 : Mp n A k lam mu *ᵥ x = c • x)
    (h2 : (Mp n A k lam mu)ᵀ *ᵥ x = c • x) : Dr n A *ᵥ x = 0 := by
  have hD : Dr n A = (1 / 2 : ℝ) • (Mp n A k lam mu - (Mp n A k lam mu)ᵀ) := by
    rw [Mp_transpose, Mp_eq_S_add_D]; module
  rw [hD, Matrix.smul_mulVec, Matrix.sub_mulVec, h1, h2, sub_self, smul_zero]

theorem rank_D_parts (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hpos : 0 < disc t lam mu) :
    ∃ f g : Nat, ∃ r s : ℝ, f + g = n - 1 ∧ r + s = ((lam - mu : ℤ) : ℝ) ∧
      r * s = ((mu - t : ℤ) : ℝ) ∧ (k : ℝ) + f * r + g * s = 0 ∧
      (toQ n (D A)).rank ≤ 2 * min f g := by
  obtain ⟨hMPp, hPpM, hPp2, hPiPp, hMPm, hPmM, hPm2, hPiPm⟩ := Pp_props h hn hpos
  have hc := cR_pos hpos
  have hc2 := cR_sq hpos
  have hc' : cR t lam mu ≠ 0 := hc.ne'
  set c := cR t lam mu with hcdef
  set M := Mp n A k lam mu with hMdef
  set P := Pp n A k t lam mu with hPdef
  set Q := Pm n A k t lam mu with hQdef
  have hPQ : P + Q = Pi1 n := by rw [hPdef, hQdef]; unfold Pp Pm; module
  have hPmQ : P - Q = (1 / c) • M := by
    rw [hPdef, hQdef]; unfold Pp Pm
    rw [← hcdef, ← hMdef]
    match_scalars <;> field_simp <;> ring1
  have hPiR : ((Pi1 n).rank : ℝ) = (n : ℝ) - 1 := by
    rw [← trace_eq_rank_of_idem _ (Pi1_mul_Pi1 hn), trace_Pi1 hn]
  have hPiN : (Pi1 n).rank + 1 = n := by
    have : ((Pi1 n).rank : ℝ) + 1 = n := by linarith
    exact_mod_cast this
  have hfR : (P.rank : ℝ) = P.trace := (trace_eq_rank_of_idem _ hPp2).symm
  have hgR : (Q.rank : ℝ) = Q.trace := (trace_eq_rank_of_idem _ hPm2).symm
  have hsumR : (P.rank : ℝ) + Q.rank = (n : ℝ) - 1 := by
    rw [hfR, hgR, ← Matrix.trace_add, hPQ, trace_Pi1 hn]
  have hfg : P.rank + Q.rank = n - 1 := by
    have : ((P.rank + Q.rank : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne')]; linarith
    exact_mod_cast this
  have hdiff : ((P.rank : ℝ) - Q.rank) * c = M.trace := by
    rw [hfR, hgR, ← Matrix.trace_sub, hPmQ, Matrix.trace_smul, smul_eq_mul]
    field_simp
  have htrM := trace_Mp h hn
  rw [← hMdef] at htrM
  have hv : (fun _ : Fin n => (1 : ℝ)) ≠ 0 := by
    intro hv; have := congrFun hv ⟨0, hn⟩; simp at this
  have hDv := mulVec_ones_of_mul_Jr hn _ (Dr_mul_Jr h)
  have hPiv := mulVec_ones_of_mul_Jr hn _ (Pi1_mul_Jr hn)
  have hMPi : Pi1 n * Mᵀ = Mᵀ := Pi1_mul_MpT h hn
  have hPPi := Pi1_mul_Pi1 hn
  have hPiPt : ∀ (b : ℝ), Pi1 n * ((1 / 2 : ℝ) • Pi1 n + b • M)ᵀ =
      ((1 / 2 : ℝ) • Pi1 n + b • M)ᵀ := by
    intro b
    rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Pi1_transpose,
      Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hPPi, hMPi]
  have hPt : P = (1 / 2 : ℝ) • Pi1 n + (1 / (2 * c)) • M := by rw [hPdef]; rfl
  have hQt : Q = (1 / 2 : ℝ) • Pi1 n + (-(1 / (2 * c))) • M := by
    rw [hQdef]; unfold Pm; rw [← hcdef, ← hMdef, neg_smul, ← sub_eq_add_neg]
  have kP := rank_add_two_rank_le (Dr n A) M P (Pi1 n) c _ hv hDv hPiv hPPi hPiPp
    (by rw [hPt]; exact hPiPt _) hMPp
    (by rw [← Matrix.transpose_mul, hPpM, Matrix.transpose_smul])
    (fun x h1 h2 => Dr_mulVec_of_eigen c x h1 h2)
  have kQ := rank_add_two_rank_le (Dr n A) M Q (Pi1 n) (-c) _ hv hDv hPiv hPPi hPiPm
    (by rw [hQt]; exact hPiPt _) hMPm
    (by rw [← Matrix.transpose_mul, hPmM, Matrix.transpose_smul])
    (fun x h1 h2 => Dr_mulVec_of_eigen (-c) x h1 h2)
  have hrank : (toQ n (D A)).rank = (Dr n A).rank := by rw [rank_toQ_eq_toR, toR_D]
  refine ⟨P.rank, Q.rank, (aR lam mu + c) / 2, (aR lam mu - c) / 2, hfg, ?_, ?_, ?_, ?_⟩
  · unfold aR; push_cast; ring
  · have hd : (disc t lam mu : ℝ) = ((lam : ℝ) - mu) ^ 2 + 4 * ((t : ℝ) - mu) := by
      unfold disc; push_cast; ring
    unfold aR; push_cast
    linear_combination (-1 / 4 : ℝ) * hc2 + (-1 / 4 : ℝ) * hd
  · have hX : (P.rank : ℝ) * ((aR lam mu + c) / 2) + Q.rank * ((aR lam mu - c) / 2) =
        ((P.rank : ℝ) + Q.rank) * aR lam mu / 2 + ((P.rank : ℝ) - Q.rank) * c / 2 := by ring
    rw [add_assoc, hX, hsumR, hdiff, htrM]
    unfold aR; push_cast; ring
  · rw [hrank]; omega

end

end DsrgRank
