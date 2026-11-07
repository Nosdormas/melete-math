import DsrgRank.Spectrum.RankLemmas

set_option autoImplicit false

namespace DsrgRank

open Matrix

section

variable {n : Nat} {A : Mat} {k t lam mu : Int}

def onesR (n : Nat) : Fin n → ℝ := fun _ => 1

/-- `A² − (Aᵀ)² = (λ − μ)D`. -/
theorem sq_sub_sq (h : IsDSRG n A k t lam mu) :
    toR n A * toR n A - (toR n A)ᵀ * (toR n A)ᵀ = aR lam mu • Dr n A := by
  have h1 := toR_sq h
  have h2 : (toR n A)ᵀ * (toR n A)ᵀ = (t : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) +
      (lam : ℝ) • (toR n A)ᵀ + (mu : ℝ) • (Jr n - 1 - (toR n A)ᵀ) := by
    rw [← Matrix.transpose_mul, h1]
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_sub,
      Matrix.transpose_one, Jr_transpose]
  rw [h1, h2]; unfold aR Dr; module

theorem A_mul_Dr (h : IsDSRG n A k t lam mu) :
    toR n A * Dr n A = Dr n A * (aR lam mu • (1 : Matrix (Fin n) (Fin n) ℝ) - (toR n A)ᵀ) := by
  have e := sq_sub_sq h
  rw [← sub_eq_zero] at e ⊢
  unfold Dr at e ⊢
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one] at e ⊢
  rw [← e]; module

/-- `AᵀD = D(aI − A)`. -/
theorem At_mul_Dr (h : IsDSRG n A k t lam mu) :
    (toR n A)ᵀ * Dr n A = Dr n A * (aR lam mu • (1 : Matrix (Fin n) (Fin n) ℝ) - toR n A) := by
  have e := sq_sub_sq h
  rw [← sub_eq_zero] at e ⊢
  unfold Dr at e ⊢
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one] at e ⊢
  rw [← e]; module

/-- `DA = (aI − Aᵀ)D`. -/
theorem Dr_mul_A (h : IsDSRG n A k t lam mu) :
    Dr n A * toR n A = (aR lam mu • (1 : Matrix (Fin n) (Fin n) ℝ) - (toR n A)ᵀ) * Dr n A := by
  have e := sq_sub_sq h
  rw [← sub_eq_zero] at e ⊢
  unfold Dr at e ⊢
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at e ⊢
  rw [← e]; module

/-- `DAᵀ = (aI − A)D`. -/
theorem Dr_mul_At (h : IsDSRG n A k t lam mu) :
    Dr n A * (toR n A)ᵀ = (aR lam mu • (1 : Matrix (Fin n) (Fin n) ℝ) - toR n A) * Dr n A := by
  have e := sq_sub_sq h
  rw [← sub_eq_zero] at e ⊢
  unfold Dr at e ⊢
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at e ⊢
  rw [← e]; module

theorem imD_eq : imD n A = LinearMap.range (Dr n A).mulVecLin := by rw [imD, toR_D]

theorem kerD_eq : kerD n A = LinearMap.ker (Dr n A).mulVecLin := by rw [kerD, toR_D]

theorem mem_eigA {x : Fin n → ℝ} {r : ℝ} : x ∈ eigA n A r ↔ toR n A *ᵥ x = r • x := by
  simp [eigA, sub_eq_zero]

theorem range_invariant {X Y : Matrix (Fin n) (Fin n) ℝ} (hXY : X * Dr n A = Dr n A * Y)
    (x : Fin n → ℝ) (hx : x ∈ LinearMap.range (Dr n A).mulVecLin) :
    X *ᵥ x ∈ LinearMap.range (Dr n A).mulVecLin := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨Y *ᵥ y, by simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hXY]⟩

theorem ker_invariant {X Y : Matrix (Fin n) (Fin n) ℝ} (hXY : Dr n A * X = Y * Dr n A)
    (x : Fin n → ℝ) (hx : x ∈ LinearMap.ker (Dr n A).mulVecLin) :
    X *ᵥ x ∈ LinearMap.ker (Dr n A).mulVecLin := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
  rw [Matrix.mulVec_mulVec, hXY, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

theorem Jr_mul_Pi1 (hn : 0 < n) : Jr n * Pi1 n = 0 := by
  have := congrArg Matrix.transpose (Pi1_mul_Jr (n := n) hn)
  rwa [Matrix.transpose_mul, Jr_transpose, Pi1_transpose, Matrix.transpose_zero] at this

theorem Pi1_mul_Dr (h : IsDSRG n A k t lam mu) : Pi1 n * Dr n A = Dr n A := by
  simp [Pi1, Matrix.sub_mul, Jr_mul_Dr h]

theorem Dr_mul_Pi1 (h : IsDSRG n A k t lam mu) : Dr n A * Pi1 n = Dr n A := by
  simp [Pi1, Matrix.mul_sub, Dr_mul_Jr h]

theorem Mp_transpose' :
    (Mp n A k lam mu)ᵀ = (2 : ℝ) • (toR n A)ᵀ - aR lam mu • (1 : Matrix (Fin n) (Fin n) ℝ) -
      betaR n k lam mu • Jr n := by
  simp [Mp, Matrix.transpose_sub, Matrix.transpose_smul, Jr_transpose]

theorem Mp_mul_Dr (h : IsDSRG n A k t lam mu) :
    Mp n A k lam mu * Dr n A = (2 : ℝ) • (toR n A * Dr n A) - aR lam mu • Dr n A := by
  simp [Mp, Matrix.sub_mul, Jr_mul_Dr h]

theorem Dr_mul_MpT (h : IsDSRG n A k t lam mu) :
    Dr n A * (Mp n A k lam mu)ᵀ = -(Mp n A k lam mu * Dr n A) := by
  rw [Mp_transpose', Mp_mul_Dr h]
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Dr_mul_Jr h, smul_zero, sub_zero,
    Dr_mul_At h, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
  module

/-- `P₊D = DP₋ᵀ`. -/
theorem Pp_mul_Dr (h : IsDSRG n A k t lam mu) :
    Pp n A k t lam mu * Dr n A = Dr n A * (Pm n A k t lam mu)ᵀ := by
  unfold Pp Pm
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_smul,
    Pi1_transpose, Matrix.mul_sub, Matrix.mul_smul, Pi1_mul_Dr h, Dr_mul_Pi1 h, Dr_mul_MpT h]
  module

/-- `P₋D = DP₊ᵀ`. -/
theorem Pm_mul_Dr (h : IsDSRG n A k t lam mu) :
    Pm n A k t lam mu * Dr n A = Dr n A * (Pp n A k t lam mu)ᵀ := by
  unfold Pp Pm
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.transpose_add, Matrix.transpose_smul,
    Pi1_transpose, Matrix.mul_add, Matrix.mul_smul, Pi1_mul_Dr h, Dr_mul_Pi1 h, Dr_mul_MpT h]
  module

theorem rank_neg_eq {m : Nat} (X : Matrix (Fin m) (Fin m) ℝ) : (-X).rank = X.rank := by
  rw [← neg_one_smul ℝ X]
  exact Matrix.rank_smul_of_mem_nonZeroDivisors X (mem_nonZeroDivisors_of_ne_zero (by norm_num))

theorem rank_Pm_mul_Dr (h : IsDSRG n A k t lam mu) :
    (Pm n A k t lam mu * Dr n A).rank = (Pp n A k t lam mu * Dr n A).rank := by
  rw [Pm_mul_Dr h, ← Matrix.rank_transpose, Matrix.transpose_mul, Matrix.transpose_transpose,
    Dr_transpose, Matrix.mul_neg, rank_neg_eq]

theorem Jr_mul_Pp (h : IsDSRG n A k t lam mu) (hn : 0 < n) : Jr n * Pp n A k t lam mu = 0 := by
  simp [Pp, Matrix.mul_add, Jr_mul_Pi1 hn, Jr_mul_Mp h hn]

theorem Jr_mul_Pm (h : IsDSRG n A k t lam mu) (hn : 0 < n) : Jr n * Pm n A k t lam mu = 0 := by
  simp [Pm, Matrix.mul_sub, Jr_mul_Pi1 hn, Jr_mul_Mp h hn]

theorem rR_eq : rR t lam mu = (aR lam mu + cR t lam mu) / 2 := by
  simp [rR, aR, cR]

theorem sR_eq : sR t lam mu = (aR lam mu - cR t lam mu) / 2 := by
  simp [sR, aR, cR]

theorem A_mul_Pp (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hpos : 0 < disc t lam mu) :
    toR n A * Pp n A k t lam mu = rR t lam mu • Pp n A k t lam mu := by
  have hM := (Pp_props h hn hpos).1
  have hJ := Jr_mul_Pp h hn
  unfold Mp at hM
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hJ, smul_zero, sub_zero] at hM
  -- hM : 2 • (A * P) − a • P = c • P
  have : toR n A * Pp n A k t lam mu =
      (1 / 2 : ℝ) • ((2 : ℝ) • (toR n A * Pp n A k t lam mu) - aR lam mu • Pp n A k t lam mu) +
        (aR lam mu / 2) • Pp n A k t lam mu := by module
  rw [this, hM, rR_eq]; module

theorem A_mul_Pm (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hpos : 0 < disc t lam mu) :
    toR n A * Pm n A k t lam mu = sR t lam mu • Pm n A k t lam mu := by
  have hM := (Pp_props h hn hpos).2.2.2.2.1
  have hJ := Jr_mul_Pm h hn
  unfold Mp at hM
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hJ, smul_zero, sub_zero] at hM
  have : toR n A * Pm n A k t lam mu =
      (1 / 2 : ℝ) • ((2 : ℝ) • (toR n A * Pm n A k t lam mu) - aR lam mu • Pm n A k t lam mu) +
        (aR lam mu / 2) • Pm n A k t lam mu := by module
  rw [this, hM, sR_eq]; module

theorem Jr_mulVec_of_mem (h : IsDSRG n A k t lam mu) {x : Fin n → ℝ}
    (hx : x ∈ LinearMap.range (Dr n A).mulVecLin) : Jr n *ᵥ x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  simp [Matrix.mulVec_mulVec, Jr_mul_Dr h]

theorem Pi1_mulVec_of_mem (h : IsDSRG n A k t lam mu) {x : Fin n → ℝ}
    (hx : x ∈ LinearMap.range (Dr n A).mulVecLin) : Pi1 n *ᵥ x = x := by
  simp [Pi1, Matrix.sub_mulVec, Matrix.smul_mulVec, Jr_mulVec_of_mem h hx]

theorem Pp_mulVec_fix (h : IsDSRG n A k t lam mu) (hpos : 0 < disc t lam mu) {x : Fin n → ℝ}
    (hx : x ∈ LinearMap.range (Dr n A).mulVecLin) (hr : toR n A *ᵥ x = rR t lam mu • x) :
    Pp n A k t lam mu *ᵥ x = x := by
  have hc : cR t lam mu ≠ 0 := (cR_pos hpos).ne'
  have hJ := Jr_mulVec_of_mem h hx
  simp only [Pp, Mp, Pi1, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, hJ, hr, smul_zero, sub_zero, rR_eq]
  match_scalars; field_simp; ring

theorem Pm_mulVec_fix (h : IsDSRG n A k t lam mu) (hpos : 0 < disc t lam mu) {x : Fin n → ℝ}
    (hx : x ∈ LinearMap.range (Dr n A).mulVecLin) (hs : toR n A *ᵥ x = sR t lam mu • x) :
    Pm n A k t lam mu *ᵥ x = x := by
  have hc : cR t lam mu ≠ 0 := (cR_pos hpos).ne'
  have hJ := Jr_mulVec_of_mem h hx
  simp only [Pm, Mp, Pi1, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, hJ, hs, smul_zero, sub_zero, sR_eq]
  match_scalars; field_simp; ring

theorem inf_eigA_r (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hpos : 0 < disc t lam mu) :
    imD n A ⊓ eigA n A (rR t lam mu) =
      LinearMap.range (Pp n A k t lam mu * Dr n A).mulVecLin := by
  apply le_antisymm
  · rintro x ⟨hxW, hxE⟩
    rw [imD_eq] at hxW
    rw [SetLike.mem_coe, mem_eigA] at hxE
    obtain ⟨y, hy⟩ := hxW
    refine ⟨y, ?_⟩
    rw [Matrix.mulVecLin_apply] at hy ⊢
    rw [← Matrix.mulVec_mulVec, hy, Pp_mulVec_fix h hpos ⟨y, hy⟩ hxE]
  · rintro x ⟨y, rfl⟩
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [imD_eq]
      exact ⟨(Pm n A k t lam mu)ᵀ *ᵥ y, by
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Pp_mul_Dr h]⟩
    · show _ ∈ eigA n A (rR t lam mu)
      rw [mem_eigA, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
        A_mul_Pp h hn hpos, Matrix.smul_mul, Matrix.smul_mulVec]

theorem inf_eigA_s (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hpos : 0 < disc t lam mu) :
    imD n A ⊓ eigA n A (sR t lam mu) =
      LinearMap.range (Pm n A k t lam mu * Dr n A).mulVecLin := by
  apply le_antisymm
  · rintro x ⟨hxW, hxE⟩
    rw [imD_eq] at hxW
    rw [SetLike.mem_coe, mem_eigA] at hxE
    obtain ⟨y, hy⟩ := hxW
    refine ⟨y, ?_⟩
    rw [Matrix.mulVecLin_apply] at hy ⊢
    rw [← Matrix.mulVec_mulVec, hy, Pm_mulVec_fix h hpos ⟨y, hy⟩ hxE]
  · rintro x ⟨y, rfl⟩
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [imD_eq]
      exact ⟨(Pp n A k t lam mu)ᵀ *ᵥ y, by
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Pm_mul_Dr h]⟩
    · show _ ∈ eigA n A (sR t lam mu)
      rw [mem_eigA, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
        A_mul_Pm h hn hpos, Matrix.smul_mul, Matrix.smul_mulVec]

theorem imD_eq_sup (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hpos : 0 < disc t lam mu) :
    imD n A = imD n A ⊓ eigA n A (rR t lam mu) ⊔ imD n A ⊓ eigA n A (sR t lam mu) := by
  apply le_antisymm _ (sup_le inf_le_left inf_le_left)
  intro x hx
  have hxW := hx
  rw [imD_eq] at hxW
  have hsplit : x = Pp n A k t lam mu *ᵥ x + Pm n A k t lam mu *ᵥ x := by
    rw [← Matrix.add_mulVec]
    have hPQ : Pp n A k t lam mu + Pm n A k t lam mu = Pi1 n := by unfold Pp Pm; module
    rw [hPQ, Pi1_mulVec_of_mem h hxW]
  rw [hsplit, inf_eigA_r h hn hpos, inf_eigA_s h hn hpos]
  obtain ⟨y, rfl⟩ := hxW
  refine Submodule.add_mem_sup ⟨y, ?_⟩ ⟨y, ?_⟩ <;>
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]

theorem eigA_disjoint (hpos : 0 < disc t lam mu) :
    eigA n A (rR t lam mu) ⊓ eigA n A (sR t lam mu) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hr, hs⟩
  rw [SetLike.mem_coe, mem_eigA] at hr hs
  have hrs : rR t lam mu - sR t lam mu ≠ 0 := by
    rw [rR_eq, sR_eq]; have := cR_pos hpos; intro e; linarith
  have : (rR t lam mu - sR t lam mu) • x = 0 := by rw [sub_smul, ← hr, ← hs, sub_self]
  rw [Submodule.mem_bot]
  exact (smul_eq_zero.mp this).resolve_left hrs

theorem multiplicities (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hpos : 0 < disc t lam mu) :
    ∃ m : ℕ, (toQ n (D A)).rank = 2 * m ∧
      Module.finrank ℝ ↥(imD n A ⊓ eigA n A (rR t lam mu)) = m ∧
      Module.finrank ℝ ↥(imD n A ⊓ eigA n A (sR t lam mu)) = m ∧
      imD n A = imD n A ⊓ eigA n A (rR t lam mu) ⊔ imD n A ⊓ eigA n A (sR t lam mu) := by
  set Wr := imD n A ⊓ eigA n A (rR t lam mu) with hWr
  set Ws := imD n A ⊓ eigA n A (sR t lam mu) with hWs
  have hr : Module.finrank ℝ ↥Wr = (Pp n A k t lam mu * Dr n A).rank := by
    rw [hWr, inf_eigA_r h hn hpos]; rfl
  have hs : Module.finrank ℝ ↥Ws = (Pp n A k t lam mu * Dr n A).rank := by
    rw [hWs, inf_eigA_s h hn hpos, ← rank_Pm_mul_Dr h]; rfl
  have hsup := imD_eq_sup h hn hpos
  rw [← hWr, ← hWs] at hsup
  have hinf : Wr ⊓ Ws = ⊥ := by
    rw [eq_bot_iff, ← eigA_disjoint (n := n) (A := A) hpos]
    exact inf_le_inf inf_le_right inf_le_right
  have e := Submodule.finrank_sup_add_finrank_inf_eq Wr Ws
  rw [hinf, finrank_bot, ← hsup, add_zero] at e
  have hrank : (toQ n (D A)).rank = Module.finrank ℝ ↥(imD n A) := by
    rw [rank_toQ_eq_toR, imD]; rfl
  refine ⟨(Pp n A k t lam mu * Dr n A).rank, ?_, hr, hs, hsup⟩
  rw [hrank, e, hr, hs]; ring

theorem SpectralLemma_struct (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hpos : 0 < disc t lam mu) :
    SpectralLemmaStruct n A t lam mu := by
  refine ⟨?_, ?_, ?_, multiplicities h hn hpos, ?_, ?_, ?_⟩
  · intro x hx
    rw [imD_eq] at hx
    obtain ⟨y, rfl⟩ := hx
    have h1 : Dr n A *ᵥ onesR n = 0 := mulVec_ones_of_mul_Jr hn _ (Dr_mul_Jr h)
    rw [Matrix.mulVecLin_apply, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      Dr_transpose, Matrix.neg_mulVec]
    change (-(Dr n A *ᵥ onesR n)) ⬝ᵥ y = 0
    rw [h1, neg_zero, zero_dotProduct]
  · intro x hx
    rw [imD_eq] at hx ⊢
    exact range_invariant (A_mul_Dr h) x hx
  · intro x hx
    rw [imD_eq] at hx ⊢
    exact range_invariant (At_mul_Dr h) x hx
  · intro x hx
    rw [kerD_eq] at hx ⊢
    exact ker_invariant (Dr_mul_A h) x hx
  · intro x hx
    rw [kerD_eq] at hx ⊢
    exact ker_invariant (Dr_mul_At h) x hx
  · intro x hx
    rw [kerD_eq, LinearMap.mem_ker, Matrix.mulVecLin_apply, Dr, Matrix.sub_mulVec,
      sub_eq_zero] at hx
    exact hx

end

end DsrgRank
