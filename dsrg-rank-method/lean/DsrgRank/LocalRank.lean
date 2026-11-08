module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import DsrgRank.KernelFrame

/-!
Defines the eigenspace of A for theta and proves local rank facts at a vertex and its out-
neighbours: eigenvectors sum to zero when theta differs from k, dimension bounds at out-neighbours
and at far vertices, and, for a root pair under 0 < t < k < n - 1, the identity dim E(theta) + 1 +
dim E(theta') = n.
-/

@[expose] public section

set_option autoImplicit false

namespace DsrgRank

open Matrix

variable {n : Nat}

def vanishOn (Z : Finset (Fin n)) : Submodule ℝ (Fin n → ℝ) where
  carrier := {u | ∀ i ∈ Z, u i = 0}
  add_mem' := by
    intro a b ha hb i hi
    simp [ha i hi, hb i hi]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro c a ha i hi
    simp [ha i hi]

theorem mem_vanishOn {Z : Finset (Fin n)} {u : Fin n → ℝ} :
    u ∈ vanishOn Z ↔ ∀ i ∈ Z, u i = 0 := Iff.rfl

theorem LocRank_count (E : Submodule ℝ (Fin n → ℝ)) (Z : Finset (Fin n)) (c : Fin n → ℝ)
    (hsupp : ∀ i, i ∉ Z → c i = 0) (i0 : Fin n) (hi0 : i0 ∈ Z) (hc0 : c i0 ≠ 0)
    (horth : ∀ u ∈ E, c ⬝ᵥ u = 0) :
    Module.finrank ℝ E + 1 ≤ Z.card + Module.finrank ℝ ↥(E ⊓ vanishOn Z) := by
  classical
  let ρ : E →ₗ[ℝ] (Z → ℝ) := LinearMap.pi fun i : Z => (LinearMap.proj (i : Fin n)).comp E.subtype
  let φ : (Z → ℝ) →ₗ[ℝ] ℝ := ∑ i : Z, c i • LinearMap.proj i
  have hφ : ∀ y : Z → ℝ, φ y = ∑ i : Z, c i * y i := by
    intro y
    simp [φ, LinearMap.sum_apply, smul_eq_mul]
  have hrange : LinearMap.range ρ ≤ LinearMap.ker φ := by
    rintro y ⟨u, rfl⟩
    rw [LinearMap.mem_ker, hφ]
    have e := horth u u.2
    simp only [dotProduct] at e
    rw [← Finset.sum_subset (Finset.subset_univ Z) (fun i _ hi => by rw [hsupp i hi, zero_mul])] at e
    rw [← Finset.sum_coe_sort Z] at e
    simpa [ρ] using e
  have hsurj : Function.Surjective φ := by
    intro r
    refine ⟨Pi.single ⟨i0, hi0⟩ (r / c i0), ?_⟩
    rw [hφ, Finset.sum_eq_single ⟨i0, hi0⟩]
    · simp
      field_simp
    · intro b _ hb
      simp [hb]
    · simp
  have hφrank : Module.finrank ℝ (LinearMap.range φ) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have hφnull := LinearMap.finrank_range_add_finrank_ker φ
  rw [hφrank, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hφnull
  have hker : Module.finrank ℝ (LinearMap.ker ρ) ≤ Module.finrank ℝ ↥(E ⊓ vanishOn Z) := by
    rw [← Submodule.finrank_map_subtype_eq E (LinearMap.ker ρ)]
    apply Submodule.finrank_mono
    rintro y ⟨u, hu, rfl⟩
    refine ⟨u.2, ?_⟩
    intro i hi
    have := congrFun (LinearMap.mem_ker.mp hu) ⟨i, hi⟩
    simpa [ρ] using this
  have hρ := LinearMap.finrank_range_add_finrank_ker ρ
  have hmono := Submodule.finrank_mono hrange
  omega

noncomputable def Eth (n : Nat) (A : Mat) (θ : ℝ) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker (Matrix.mulVecLin (toR n A - θ • (1 : Matrix (Fin n) (Fin n) ℝ)))

theorem mem_Eth {A : Mat} {θ : ℝ} {u : Fin n → ℝ} :
    u ∈ Eth n A θ ↔ (toR n A - θ • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u = 0 := by
  rw [Eth, LinearMap.mem_ker, Matrix.mulVecLin_apply]

section

variable {A : Mat} {k t lam mu : Int} {θ : ℝ}

theorem LocRank_sum_zero (h : IsDSRG n A k t lam mu) (hθ : θ ≠ k) {u : Fin n → ℝ}
    (hu : u ∈ Eth n A θ) : ∑ i, u i = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  have e := congrArg (fun M => (M *ᵥ u) ⟨0, hn⟩) (KerFrame_Jsub h θ)
  rw [← Matrix.mulVec_mulVec, (mem_Eth).1 hu, Matrix.mulVec_zero, Matrix.smul_mulVec] at e
  simp [Jr, Matrix.mulVec, dotProduct] at e
  rcases e with e | e
  · exact absurd (sub_eq_zero.mp e).symm hθ
  · exact e

theorem LocRank_out (h : IsDSRG n A k t lam mu) (hθ : θ ≠ k) (x w : Fin n)
    (hw : θ ≠ -1 ∨ (A x w = 0 ∧ w ≠ x)) :
    Module.finrank ℝ (Eth n A θ) + 1 ≤
      (Finset.univ.filter (fun i : Fin n => A x i = 0)).card +
        Module.finrank ℝ ↥(Eth n A θ ⊓ vanishOn (Finset.univ.filter (fun i : Fin n => A x i = 0))) := by
  set Z := Finset.univ.filter (fun i : Fin n => A x i = 0) with hZ
  let c : Fin n → ℝ := fun i => 1 - (toR n A - θ • (1 : Matrix (Fin n) (Fin n) ℝ)) x i
  have hxx : A x x = 0 := h.2.1 x x.isLt
  have hsupp : ∀ i, i ∉ Z → c i = 0 := by
    intro i hi
    have hi' : A x i ≠ 0 := by simpa [hZ] using hi
    have h1 : A x i = 1 := (h.1 x x.isLt i i.isLt).resolve_left hi'
    have hxi : x ≠ i := by
      intro e
      rw [← e, hxx] at h1
      exact absurd h1 (by norm_num)
    simp [c, toR, h1, Matrix.one_apply_ne hxi]
  have horth : ∀ u ∈ Eth n A θ, c ⬝ᵥ u = 0 := by
    intro u hu
    have hs := LocRank_sum_zero h hθ hu
    have hrow := congrFun ((mem_Eth).1 hu) x
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hrow
    simp only [c, dotProduct, sub_mul, one_mul, Finset.sum_sub_distrib, hs, hrow, sub_zero]
  rcases hw with hθ1 | ⟨hxw, hwx⟩
  · refine LocRank_count _ Z c hsupp x (by simp [hZ, hxx]) ?_ horth
    have : c x = 1 + θ := by simp [c, toR, hxx]
    rw [this]
    intro e
    exact hθ1 (by linarith)
  · refine LocRank_count _ Z c hsupp w (by simp [hZ, hxw]) ?_ horth
    simp [c, toR, hxw, Matrix.one_apply_ne (Ne.symm hwx)]

theorem LocRank_far (h : IsDSRG n A k t lam mu) (x o : Fin n) (ho : A x o = 1) :
    Module.finrank ℝ (Eth n A θ) + 1 ≤
      (Finset.univ.filter (fun i : Fin n => A x i = 1 ∨ i = x)).card +
        Module.finrank ℝ
          ↥(Eth n A θ ⊓ vanishOn (Finset.univ.filter (fun i : Fin n => A x i = 1 ∨ i = x))) := by
  set Z := Finset.univ.filter (fun i : Fin n => A x i = 1 ∨ i = x) with hZ
  let c : Fin n → ℝ := fun i => (toR n A - θ • (1 : Matrix (Fin n) (Fin n) ℝ)) x i
  have hsupp : ∀ i, i ∉ Z → c i = 0 := by
    intro i hi
    have hi' : ¬(A x i = 1 ∨ i = x) := by simpa [hZ] using hi
    push Not at hi'
    have h0 : A x i = 0 := (h.1 x x.isLt i i.isLt).resolve_right hi'.1
    simp [c, toR, h0, Matrix.one_apply_ne (Ne.symm hi'.2)]
  have horth : ∀ u ∈ Eth n A θ, c ⬝ᵥ u = 0 := by
    intro u hu
    have hrow := congrFun ((mem_Eth).1 hu) x
    simpa [Matrix.mulVec, c] using hrow
  have hox : o ≠ x := by
    intro e
    rw [e, h.2.1 x x.isLt] at ho
    exact absurd ho (by norm_num)
  refine LocRank_count _ Z c hsupp o (by simp [hZ, ho]) ?_ horth
  simp [c, toR, ho, Matrix.one_apply_ne (Ne.symm hox)]

theorem LocRank_card_out (h : IsDSRG n A k t lam mu) (x : Fin n) :
    (((Finset.univ.filter (fun i : Fin n => A x i = 1)).card : Nat) : Int) = k := by
  have hrow := h.2.2.1 x x.isLt
  rw [sumBelow_eq_fin] at hrow
  rw [← hrow, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rcases h.1 x x.isLt i i.isLt with h0 | h1
  · simp [h0]
  · simp [h1]

theorem LocRank_out_dim (h : IsDSRG n A k t lam mu) (hθ : θ ≠ k) (x w : Fin n)
    (hw : θ ≠ -1 ∨ (A x w = 0 ∧ w ≠ x)) (m' : Nat)
    (hdim : Module.finrank ℝ (Eth n A θ) + 1 + m' = n) :
    k ≤ (m' : Int) +
      Module.finrank ℝ ↥(Eth n A θ ⊓ vanishOn (Finset.univ.filter (fun i : Fin n => A x i = 0))) := by
  have hb := LocRank_out h hθ x w hw
  have hc := LocRank_card_out h x
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n => A x i = 1)
  have hneg : Finset.univ.filter (fun i : Fin n => ¬A x i = 1) =
      Finset.univ.filter (fun i : Fin n => A x i = 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases h.1 x x.isLt i i.isLt with h0 | h1
    · simp [h0]
    · simp [h1]
  rw [hneg, Finset.card_univ, Fintype.card_fin] at hsplit
  omega

theorem LocRank_far_dim (h : IsDSRG n A k t lam mu) (x o : Fin n) (ho : A x o = 1) (m' : Nat)
    (hdim : Module.finrank ℝ (Eth n A θ) + 1 + m' = n) :
    (n : Int) - k - 1 ≤ (m' : Int) +
      Module.finrank ℝ
        ↥(Eth n A θ ⊓ vanishOn (Finset.univ.filter (fun i : Fin n => A x i = 1 ∨ i = x))) := by
  have hb := LocRank_far (θ := θ) h x o ho
  have hc := LocRank_card_out h x
  have hxx : A x x = 0 := h.2.1 x x.isLt
  have hcl : (Finset.univ.filter (fun i : Fin n => A x i = 1 ∨ i = x)) =
      insert x (Finset.univ.filter (fun i : Fin n => A x i = 1)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    tauto
  have hxn : x ∉ Finset.univ.filter (fun i : Fin n => A x i = 1) := by
    simp [hxx]
  rw [hcl, Finset.card_insert_of_notMem hxn] at hb
  rw [hcl]
  omega

end

section duval

variable {A : Mat} {k t lam mu : Int} {θ θ' : ℝ}

theorem LocRank_hdim (h : IsDSRG n A k t lam mu) (ht : 0 < t) (htk : t < k)
    (hkn : k < (n : Int) - 1) (hr : IsRootPair t lam mu θ θ') :
    Module.finrank ℝ (Eth n A θ) + 1 + Module.finrank ℝ (eigA n A θ') = n := by
  have hn : 0 < n := by omega
  have hpos := disc_pos h ht htk hkn
  have hμ := (mu_pos h ht htk hkn).ne'
  obtain ⟨-, -, hsum, -⟩ := spectrum_counts h hn hpos hμ
  have hE : Eth n A θ = eigA n A θ := rfl
  rw [hE]
  rcases root_cases hpos hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

theorem LocRank_out_duval (h : IsDSRG n A k t lam mu) (ht : 0 < t) (htk : t < k)
    (hkn : k < (n : Int) - 1) (hr : IsRootPair t lam mu θ θ') (x w : Fin n)
    (hw : θ ≠ -1 ∨ (A x w = 0 ∧ w ≠ x)) :
    k ≤ (Module.finrank ℝ (eigA n A θ') : Int) +
      Module.finrank ℝ
        ↥(Eth n A θ ⊓ vanishOn (Finset.univ.filter (fun i : Fin n => A x i = 0))) := by
  have hn : 0 < n := by omega
  have hμ := (mu_pos h ht htk hkn).ne'
  have hθk : θ ≠ k := fun e => (k_ne_root h hn hμ hr).1 e.symm
  exact LocRank_out_dim h hθk x w hw _ (LocRank_hdim h ht htk hkn hr)

theorem LocRank_far_duval (h : IsDSRG n A k t lam mu) (ht : 0 < t) (htk : t < k)
    (hkn : k < (n : Int) - 1) (hr : IsRootPair t lam mu θ θ') (x o : Fin n) (ho : A x o = 1) :
    (n : Int) - k - 1 ≤ (Module.finrank ℝ (eigA n A θ') : Int) +
      Module.finrank ℝ
        ↥(Eth n A θ ⊓ vanishOn (Finset.univ.filter (fun i : Fin n => A x i = 1 ∨ i = x))) :=
  LocRank_far_dim h x o ho _ (LocRank_hdim h ht htk hkn hr)

end duval

end DsrgRank
