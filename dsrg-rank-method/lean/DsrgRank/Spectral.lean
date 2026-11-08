module

public import DsrgRank.Spectrum.Proof

/-!
Defines the root pair of a DSRG: theta + theta' = lambda - mu and theta theta' = mu - t. Proves that
the roots are the numbers rR and sR when the discriminant is positive, the multiplicity equations of
the eigenvalues, and that every vertex with out-degree k > 0 has an out-arc.
-/

@[expose] public section

set_option autoImplicit false

namespace DsrgRank

open Matrix

def IsRootPair (t lam mu : Int) (θ θ' : ℝ) : Prop :=
  θ + θ' = (lam : ℝ) - mu ∧ θ * θ' = (mu : ℝ) - t

theorem IsRootPair.symm {t lam mu : Int} {θ θ' : ℝ} (hr : IsRootPair t lam mu θ θ') :
    IsRootPair t lam mu θ' θ :=
  ⟨by rw [add_comm]; exact hr.1, by rw [mul_comm]; exact hr.2⟩

theorem sumBelow_zero (n : Nat) : sumBelow n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumBelow, ih]

section

variable {n : Nat} {A : Mat} {k t lam mu : Int} {θ θ' : ℝ}

theorem disc_cast : (disc t lam mu : ℝ) = ((lam : ℝ) - mu) ^ 2 + 4 * ((t : ℝ) - mu) := by
  unfold disc; push_cast; ring

theorem isRootPair_rs (hd : 0 ≤ disc t lam mu) :
    IsRootPair t lam mu (rR t lam mu) (sR t lam mu) := by
  have hc : cR t lam mu * cR t lam mu = (disc t lam mu : ℝ) :=
    Real.mul_self_sqrt (by exact_mod_cast hd)
  rw [disc_cast] at hc
  refine ⟨?_, ?_⟩ <;> rw [rR_eq, sR_eq] <;> unfold aR
  · ring
  · linear_combination (-1 / 4 : ℝ) * hc

/-- `r − s = √Δ`. -/
theorem rR_sub_sR : rR t lam mu - sR t lam mu = cR t lam mu := by
  rw [rR_eq, sR_eq]; ring

theorem rR_sub_sR_sq (hd : 0 ≤ disc t lam mu) :
    (rR t lam mu - sR t lam mu) ^ 2 = (disc t lam mu : ℝ) := by
  rw [rR_sub_sR, sq]; exact Real.mul_self_sqrt (by exact_mod_cast hd)

theorem root_cases (hpos : 0 < disc t lam mu) (hr : IsRootPair t lam mu θ θ') :
    (θ = rR t lam mu ∧ θ' = sR t lam mu) ∨ (θ = sR t lam mu ∧ θ' = rR t lam mu) := by
  obtain ⟨h1, h2⟩ := isRootPair_rs (t := t) (lam := lam) (mu := mu) hpos.le
  obtain ⟨e1, e2⟩ := hr
  have hq : (θ - rR t lam mu) * (θ - sR t lam mu) = 0 := by
    linear_combination θ * e1 - e2 - θ * h1 + h2
  rcases mul_eq_zero.mp hq with e | e
  · left; refine ⟨sub_eq_zero.mp e, ?_⟩; have := sub_eq_zero.mp e; linarith
  · right; refine ⟨sub_eq_zero.mp e, ?_⟩; have := sub_eq_zero.mp e; linarith

theorem sub_mul_sub_eq (h : IsDSRG n A k t lam mu) (hr : IsRootPair t lam mu θ θ') :
    (toR n A - θ' • (1 : Matrix (Fin n) (Fin n) ℝ)) * (toR n A - θ • 1) = (mu : ℝ) • Jr n := by
  obtain ⟨h1, h2⟩ := hr
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, toR_sq h]
  match_scalars <;>
    first
    | ring1
    | linear_combination h1
    | linear_combination -h1
    | linear_combination h2

theorem sub_r_mul_sub_s (h : IsDSRG n A k t lam mu) (hd : 0 ≤ disc t lam mu) :
    (toR n A - rR t lam mu • (1 : Matrix (Fin n) (Fin n) ℝ)) * (toR n A - sR t lam mu • 1) =
      (mu : ℝ) • Jr n :=
  sub_mul_sub_eq h (isRootPair_rs hd).symm

theorem k_sub_mul_k_sub (h : IsDSRG n A k t lam mu) (hn : 0 < n)
    (hr : IsRootPair t lam mu θ θ') : ((k : ℝ) - θ) * ((k : ℝ) - θ') = (n : ℝ) * mu := by
  have hk := k_sq h hn
  obtain ⟨h1, h2⟩ := hr
  linear_combination hk - (k : ℝ) * h1 + h2

theorem exists_arc (h : IsDSRG n A k t lam mu) {i : Nat} (hi : i < n) (hk : 0 < k) :
    ∃ j, j < n ∧ A i j = 1 := by
  by_contra hno
  push Not at hno
  have e : sumBelow n (fun l => A i l) = sumBelow n (fun _ => 0) :=
    sumBelow_congr (fun l hl => (h.1 i hi l hl).resolve_right (hno l hl))
  rw [h.2.2.1 i hi, sumBelow_zero] at e
  omega

theorem lam_le_of_arc (h : IsDSRG n A k t lam mu) {i j : Nat} (hi : i < n) (hj : j < n)
    (hij : A i j = 1) : lam ≤ k - 1 := by
  have hne : i ≠ j := by
    rintro rfl; rw [h.2.1 i hi] at hij; exact absurd hij (by decide)
  have e := h.2.2.2.2 i hi j hj
  rw [show delta i j = 0 by simp [delta, hne], hij] at e
  have hle : sumBelow n (fun l => A i l * A l j) ≤
      sumBelow n (fun l => A i l - if l = j then 1 else 0) := by
    apply sumBelow_le
    intro l hl
    by_cases e' : l = j
    · subst e'; simp [h.2.1 l hl, hij]
    · rw [show (if l = j then (1 : Int) else 0) = 0 by simp [e'], sub_zero]; exact (pair_facts (h.1 i hi l hl) (h.1 l hl j hj)).2.1
  rw [sumBelow_sub, h.2.2.1 i hi, sumBelow_single 1 hj, e] at hle
  linarith

theorem mu_pos (h : IsDSRG n A k t lam mu) (ht : 0 < t) (htk : t < k)
    (hkn : k < (n : Int) - 1) : 0 < mu := by
  have hn : 0 < n := by omega
  obtain ⟨j, hj, hij⟩ := exists_arc h hn (by omega : 0 < k)
  have hlam := lam_le_of_arc h hn hj hij
  have hkR := k_sq h hn
  have hkZ : k ^ 2 = t + lam * k + mu * ((n : Int) - 1 - k) := by exact_mod_cast hkR
  by_contra hmu
  push Not at hmu
  nlinarith [mul_le_mul_of_nonneg_right hlam (by omega : (0 : Int) ≤ k),
    mul_le_mul_of_nonneg_right hmu (by omega : (0 : Int) ≤ (n : Int) - 1 - k)]

theorem k_ne_root (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hμ : mu ≠ 0)
    (hr : IsRootPair t lam mu θ θ') : (k : ℝ) ≠ θ ∧ (k : ℝ) ≠ θ' := by
  have e := k_sub_mul_k_sub h hn hr
  have hne : (n : ℝ) * mu ≠ 0 := mul_ne_zero (by exact_mod_cast hn.ne') (by exact_mod_cast hμ)
  rw [← e] at hne
  exact ⟨sub_ne_zero.mp (left_ne_zero_of_mul hne), sub_ne_zero.mp (right_ne_zero_of_mul hne)⟩

theorem Jr_mulVec_of_eig (h : IsDSRG n A k t lam mu) {x : Fin n → ℝ}
    (hx : toR n A *ᵥ x = θ • x) (hk : (k : ℝ) ≠ θ) : Jr n *ᵥ x = 0 := by
  have e : Jr n *ᵥ (toR n A *ᵥ x) = (k : ℝ) • (Jr n *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Jr_mul_toR h, Matrix.smul_mulVec]
  rw [hx, Matrix.mulVec_smul] at e
  have e2 : ((k : ℝ) - θ) • (Jr n *ᵥ x) = 0 := by rw [sub_smul, ← e, sub_self]
  exact (smul_eq_zero.mp e2).resolve_left (sub_ne_zero.mpr hk)

theorem Pp_mulVec_of_eig (hpos : 0 < disc t lam mu) {x : Fin n → ℝ} (hJ : Jr n *ᵥ x = 0)
    (hr : toR n A *ᵥ x = rR t lam mu • x) : Pp n A k t lam mu *ᵥ x = x := by
  have hc : cR t lam mu ≠ 0 := (cR_pos hpos).ne'
  simp only [Pp, Mp, Pi1, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, hJ, hr, smul_zero, sub_zero, rR_eq]
  match_scalars; field_simp; ring

theorem Pm_mulVec_of_eig (hpos : 0 < disc t lam mu) {x : Fin n → ℝ} (hJ : Jr n *ᵥ x = 0)
    (hs : toR n A *ᵥ x = sR t lam mu • x) : Pm n A k t lam mu *ᵥ x = x := by
  have hc : cR t lam mu ≠ 0 := (cR_pos hpos).ne'
  simp only [Pm, Mp, Pi1, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, hJ, hs, smul_zero, sub_zero, sR_eq]
  match_scalars; field_simp; ring

theorem eigA_r_eq (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hpos : 0 < disc t lam mu)
    (hk : (k : ℝ) ≠ rR t lam mu) :
    eigA n A (rR t lam mu) = LinearMap.range (Pp n A k t lam mu).mulVecLin := by
  apply le_antisymm
  · intro x hx
    rw [mem_eigA] at hx
    exact ⟨x, by
      rw [Matrix.mulVecLin_apply]; exact Pp_mulVec_of_eig hpos (Jr_mulVec_of_eig h hx hk) hx⟩
  · rintro x ⟨y, rfl⟩
    rw [mem_eigA, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, A_mul_Pp h hn hpos,
      Matrix.smul_mulVec]

theorem eigA_s_eq (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hpos : 0 < disc t lam mu)
    (hk : (k : ℝ) ≠ sR t lam mu) :
    eigA n A (sR t lam mu) = LinearMap.range (Pm n A k t lam mu).mulVecLin := by
  apply le_antisymm
  · intro x hx
    rw [mem_eigA] at hx
    exact ⟨x, by
      rw [Matrix.mulVecLin_apply]; exact Pm_mulVec_of_eig hpos (Jr_mulVec_of_eig h hx hk) hx⟩
  · rintro x ⟨y, rfl⟩
    rw [mem_eigA, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, A_mul_Pm h hn hpos,
      Matrix.smul_mulVec]

theorem rank_Pp_Pm (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hpos : 0 < disc t lam mu) :
    (Pp n A k t lam mu).rank + (Pm n A k t lam mu).rank = n - 1 ∧
    (k : ℝ) + (Pp n A k t lam mu).rank * rR t lam mu +
      (Pm n A k t lam mu).rank * sR t lam mu = 0 := by
  obtain ⟨_, _, hPp2, _, _, _, hPm2, _⟩ := Pp_props h hn hpos
  have hc' : cR t lam mu ≠ 0 := (cR_pos hpos).ne'
  set c := cR t lam mu with hcdef
  set M := Mp n A k lam mu with hMdef
  set P := Pp n A k t lam mu with hPdef
  set Q := Pm n A k t lam mu with hQdef
  have hPQ : P + Q = Pi1 n := by rw [hPdef, hQdef]; unfold Pp Pm; module
  have hPmQ : P - Q = (1 / c) • M := by
    rw [hPdef, hQdef]; unfold Pp Pm
    rw [← hcdef, ← hMdef]
    match_scalars <;> field_simp <;> ring1
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
  refine ⟨hfg, ?_⟩
  rw [rR_eq, sR_eq, ← hcdef]
  have hX : (P.rank : ℝ) * ((aR lam mu + c) / 2) + Q.rank * ((aR lam mu - c) / 2) =
      ((P.rank : ℝ) + Q.rank) * aR lam mu / 2 + ((P.rank : ℝ) - Q.rank) * c / 2 := by ring
  rw [add_assoc, hX, hsumR, hdiff, htrM]
  unfold aR; push_cast; ring

theorem spectrum_counts (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hpos : 0 < disc t lam mu)
    (hμ : mu ≠ 0) :
    Module.finrank ℝ (eigA n A (rR t lam mu)) = (Pp n A k t lam mu).rank ∧
    Module.finrank ℝ (eigA n A (sR t lam mu)) = (Pm n A k t lam mu).rank ∧
    Module.finrank ℝ (eigA n A (rR t lam mu)) + Module.finrank ℝ (eigA n A (sR t lam mu)) =
      n - 1 ∧
    (k : ℝ) + Module.finrank ℝ (eigA n A (rR t lam mu)) * rR t lam mu +
      Module.finrank ℝ (eigA n A (sR t lam mu)) * sR t lam mu = 0 := by
  obtain ⟨hkr, hks⟩ := k_ne_root h hn hμ (isRootPair_rs hpos.le)
  have hf : Module.finrank ℝ (eigA n A (rR t lam mu)) = (Pp n A k t lam mu).rank := by
    rw [eigA_r_eq h hn hpos hkr]; rfl
  have hg : Module.finrank ℝ (eigA n A (sR t lam mu)) = (Pm n A k t lam mu).rank := by
    rw [eigA_s_eq h hn hpos hks]; rfl
  obtain ⟨h1, h2⟩ := rank_Pp_Pm h hn hpos
  exact ⟨hf, hg, by rw [hf, hg]; exact h1, by rw [hf, hg]; exact h2⟩

/-- `rank(A − θI) + dim E_θ = n`. -/
theorem rank_add_finrank_eigA (θ : ℝ) :
    (toR n A - θ • (1 : Matrix (Fin n) (Fin n) ℝ)).rank + Module.finrank ℝ (eigA n A θ) = n := by
  have := LinearMap.finrank_range_add_finrank_ker
    (toR n A - θ • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVecLin
  rw [Module.finrank_fin_fun] at this
  exact this

theorem rank_sub_root (h : IsDSRG n A k t lam mu) (hn : 0 < n) (hpos : 0 < disc t lam mu)
    (hμ : mu ≠ 0) (hr : IsRootPair t lam mu θ θ') :
    (toR n A - θ • (1 : Matrix (Fin n) (Fin n) ℝ)).rank = 1 + Module.finrank ℝ (eigA n A θ') := by
  have hrk := rank_add_finrank_eigA (n := n) (A := A) θ
  have hsum := (spectrum_counts h hn hpos hμ).2.2.1
  rcases root_cases hpos hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

theorem rank_sub_root_duval (h : IsDSRG n A k t lam mu) (ht : 0 < t) (htk : t < k)
    (hkn : k < (n : Int) - 1) (hr : IsRootPair t lam mu θ θ') :
    (toR n A - θ • (1 : Matrix (Fin n) (Fin n) ℝ)).rank = 1 + Module.finrank ℝ (eigA n A θ') :=
  rank_sub_root h (by omega) (disc_pos h ht htk hkn) (mu_pos h ht htk hkn).ne' hr

end

end DsrgRank
