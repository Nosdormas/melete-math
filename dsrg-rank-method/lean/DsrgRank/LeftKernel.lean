module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import DsrgRank.LocalRank

/-!
For lambda = 1 and t = 2 mu, defines the left kernel of A - I at a vertex x and its out-
neighbourhood, proves identities for it and lower bounds on its dimension, and shows that the
profile space of the parameter set (55, 16, 12, 1, 6) has dimension at least 7 at each vertex.
-/

@[expose] public section

set_option autoImplicit false

namespace DsrgRank

open Matrix

section

variable {n : Nat} {A : Mat} {k t mu : Int}

def outNbhd (n : Nat) (A : Mat) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => i = x ∨ A x i = 1)

theorem mem_outNbhd {x i : Fin n} : i ∈ outNbhd n A x ↔ (i = x ∨ A x i = 1) := by
  simp [outNbhd]

noncomputable def leftKer (n : Nat) (A : Mat) (k : Int) (x : Fin n) :
    Submodule ℝ (Fin n → ℝ) :=
  vanishOn (Finset.univ \ outNbhd n A x) ⊓ LinearMap.ker (Kth n A k 1)ᵀ.mulVecLin

theorem LeftKer_col (w : Fin n → ℝ) (z : Fin n) :
    ((Kth n A k 1)ᵀ *ᵥ w) z =
      (n : ℝ) * ((∑ i : Fin n, (A i z : ℝ) * w i) - w z) - ((k : ℝ) - 1) * ∑ i : Fin n, w i := by
  have hK : ∀ i : Fin n, (Kth n A k 1) i z =
      (n : ℝ) * ((A i z : ℝ) - if i = z then 1 else 0) - ((k : ℝ) - 1) := by
    intro i
    by_cases e : i = z
    · subst e
      simp [Kth, toR, Jr]
    · simp [Kth, toR, Jr, e]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hK]
  have e1 : ∀ i : Fin n, ((n : ℝ) * ((A i z : ℝ) - if i = z then 1 else 0) - ((k : ℝ) - 1)) * w i =
      (n : ℝ) * ((A i z : ℝ) * w i) - (n : ℝ) * (if i = z then w i else 0) - ((k : ℝ) - 1) * w i := by
    intro i
    by_cases e : i = z <;> simp [e] <;> ring
  rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq']
  simp
  ring

theorem LeftKer_lam (h : IsDSRG n A k t 1 mu) {x z : Fin n} (hxz : A x z = 1) :
    ∑ i : Fin n, (A x i : ℝ) * (A i z : ℝ) = 1 := by
  have hne : (x : Nat) ≠ z := by
    intro e
    have : x = z := Fin.ext e
    subst this
    rw [h.2.1 x x.isLt] at hxz
    exact absurd hxz (by decide)
  have e := h.2.2.2.2 x x.isLt z z.isLt
  rw [sumBelow_eq_fin, hxz] at e
  simp only [delta, hne, ite_false] at e
  have eR := congrArg (fun q : ℤ => (q : ℝ)) e
  push_cast at eR
  rw [eR]
  ring

theorem LeftKer_eqs (h : IsDSRG n A k t 1 mu) (hn : 0 < n) (hk : 0 < k) {x : Fin n}
    {w : Fin n → ℝ} (hw : w ∈ leftKer n A k x) :
    (∀ y z : Fin n, A x y = 1 → A x z = 1 → A y z = 1 → w y = w z) ∧
    (∑ i : Fin n, (A i x : ℝ) * w i = 2 * w x) ∧
    (∀ z : Fin n, z ≠ x → A x z ≠ 1 → ∑ i : Fin n, (A i z : ℝ) * w i = w x) ∧
    ((n : ℝ) * w x = ((k : ℝ) - 1) * ∑ i : Fin n, w i) := by
  classical
  have zo : ∀ i j : Fin n, A i j = 0 ∨ A i j = 1 := fun i j => h.1 i i.isLt j j.isLt
  have hxx : A x x = 0 := h.2.1 x x.isLt
  obtain ⟨hsupp, hker⟩ := hw
  have hzero : ∀ i : Fin n, i ≠ x → A x i ≠ 1 → w i = 0 := by
    intro i hi hxi
    apply (mem_vanishOn.1 hsupp) i
    rw [Finset.mem_sdiff, mem_outNbhd]
    exact ⟨Finset.mem_univ _, by rintro (e | e) <;> contradiction⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set κ : ℝ := ((k : ℝ) - 1) * (∑ i : Fin n, w i) / n with hκ
  have hcol : ∀ z : Fin n, (∑ i : Fin n, (A i z : ℝ) * w i) - w z = κ := by
    intro z
    have e := congrFun (LinearMap.mem_ker.1 hker) z
    rw [Matrix.mulVecLin_apply, LeftKer_col, Pi.zero_apply] at e
    rw [hκ, eq_div_iff hnR.ne']
    linarith
  have hsplit : ∀ z : Fin n, A x z = 1 →
      ∑ i : Fin n, (A i z : ℝ) * w i = w x + ∑ i : Fin n, ((A x i : ℝ) * (A i z : ℝ)) * w i := by
    intro z hxz
    have term : ∀ i : Fin n, (A i z : ℝ) * w i =
        (if i = x then w x else 0) + ((A x i : ℝ) * (A i z : ℝ)) * w i := by
      intro i
      by_cases ei : i = x
      · subst ei
        simp [hxz, hxx]
      · rcases zo x i with e | e
        · rw [hzero i ei (by rw [e]; decide)]
          simp [ei]
        · simp [ei, e]
    rw [Finset.sum_congr rfl (fun i _ => term i), Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  have hwt : ∀ i z : Fin n, (A x i : ℝ) * (A i z : ℝ) = 0 ∨
      ((A x i : ℝ) * (A i z : ℝ) = 1 ∧ A x i = 1) := by
    intro i z
    rcases zo x i with e1 | e1 <;> rcases zo i z with e2 | e2 <;> simp [e1, e2]
  have hO : (Finset.univ.filter (fun i : Fin n => A x i = 1)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hemp
    have hrow := h.2.2.1 x x.isLt
    rw [sumBelow_eq_fin] at hrow
    have : ∑ i : Fin n, A x i = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rcases zo x i with e | e
      · exact e
      · exact absurd e (hemp (Finset.mem_univ i))
    omega
  obtain ⟨zM, hzM, hmax⟩ := Finset.exists_max_image _ w hO
  obtain ⟨zm, hzm, hmin⟩ := Finset.exists_min_image _ w hO
  rw [Finset.mem_filter] at hzM hzm
  have hle : ∀ z : Fin n, A x z = 1 →
      ∑ i : Fin n, ((A x i : ℝ) * (A i z : ℝ)) * w i ≤ w zM := by
    intro z hxz
    calc ∑ i : Fin n, ((A x i : ℝ) * (A i z : ℝ)) * w i
        ≤ ∑ i : Fin n, ((A x i : ℝ) * (A i z : ℝ)) * w zM := by
          apply Finset.sum_le_sum
          intro i _
          rcases hwt i z with e | ⟨e, e'⟩
          · rw [e]; simp
          · rw [e, one_mul, one_mul]
            exact hmax i (Finset.mem_filter.2 ⟨Finset.mem_univ _, e'⟩)
      _ = w zM := by rw [← Finset.sum_mul, LeftKer_lam h hxz, one_mul]
  have hge : ∀ z : Fin n, A x z = 1 →
      w zm ≤ ∑ i : Fin n, ((A x i : ℝ) * (A i z : ℝ)) * w i := by
    intro z hxz
    calc w zm = ∑ i : Fin n, ((A x i : ℝ) * (A i z : ℝ)) * w zm := by
          rw [← Finset.sum_mul, LeftKer_lam h hxz, one_mul]
      _ ≤ ∑ i : Fin n, ((A x i : ℝ) * (A i z : ℝ)) * w i := by
          apply Finset.sum_le_sum
          intro i _
          rcases hwt i z with e | ⟨e, e'⟩
          · rw [e]; simp
          · rw [e, one_mul, one_mul]
            exact hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ _, e'⟩)
  have h1 := hcol zM
  rw [hsplit zM hzM.2] at h1
  have h2 := hcol zm
  rw [hsplit zm hzm.2] at h2
  have hδ : w x = κ := by
    have a1 := hle zM hzM.2
    have a2 := hge zm hzm.2
    linarith
  have hP : ∀ z : Fin n, A x z = 1 → w z = ∑ i : Fin n, ((A x i : ℝ) * (A i z : ℝ)) * w i := by
    intro z hxz
    have e := hcol z
    rw [hsplit z hxz] at e
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro y z hxy hxz hyz
    rw [hP z hxz]
    have hsum := LeftKer_lam h hxz
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ y)] at hsum
    have hy1 : (A x y : ℝ) * (A y z : ℝ) = 1 := by simp [hxy, hyz]
    rw [hy1] at hsum
    have hrest : ∑ i ∈ Finset.univ.erase y, (A x i : ℝ) * (A i z : ℝ) = 0 := by linarith
    have hnn : ∀ i ∈ Finset.univ.erase y, (0 : ℝ) ≤ (A x i : ℝ) * (A i z : ℝ) := by
      intro i _
      rcases hwt i z with e | ⟨e, _⟩
      · rw [e]
      · rw [e]; norm_num
    have hz0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hrest
    rw [Finset.sum_eq_single y]
    · rw [hy1, one_mul]
    · intro i _ hi
      rw [hz0 i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩), zero_mul]
    · intro hy
      exact absurd (Finset.mem_univ y) hy
  ·
    have e := hcol x
    linarith
  ·
    intro z hz hxz
    have e := hcol z
    rw [hzero z hz hxz] at e
    linarith
  · rw [hδ, hκ]
    field_simp

/-- `|{x} ∪ Γ⁺(x)| = k + 1`. -/
theorem LeftKer_card (h : IsDSRG n A k t 1 mu) (x : Fin n) :
    ((outNbhd n A x).card : ℤ) = k + 1 := by
  classical
  have zo : ∀ i j : Fin n, A i j = 0 ∨ A i j = 1 := fun i j => h.1 i i.isLt j j.isLt
  have hxx : A x x = 0 := h.2.1 x x.isLt
  have hterm : ∀ i : Fin n, (if (i = x ∨ A x i = 1) then (1 : ℤ) else 0) =
      (if i = x then 1 else 0) + A x i := by
    intro i
    by_cases hi : i = x
    · subst hi
      simp [hxx]
    · rcases zo x i with e | e <;> simp [hi, e]
  have hc : ((outNbhd n A x).card : ℤ) =
      ∑ i : Fin n, (if (i = x ∨ A x i = 1) then (1 : ℤ) else 0) := by
    rw [outNbhd, Finset.card_filter]
    push_cast
    rfl
  have hrow := h.2.2.1 x x.isLt
  rw [sumBelow_eq_fin] at hrow
  rw [hc, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, hrow]
  simp
  ring

theorem LeftKer_roots (htm : t = 2 * mu) : IsRootPair t 1 mu 1 (-(mu : ℝ)) := by
  refine ⟨?_, ?_⟩
  · push_cast
    ring
  · rw [htm]
    push_cast
    ring

theorem LeftKer_dim (h : IsDSRG n A k t 1 mu) (ht : 0 < t) (htk : t < k) (hkn : k < (n : Int) - 1)
    (htm : t = 2 * mu) (x : Fin n) :
    k + 1 - (Module.finrank ℝ (eigA n A (-(mu : ℝ))) : ℤ) ≤
      (Module.finrank ℝ (leftKer n A k x) : ℤ) := by
  classical
  set S := outNbhd n A x with hSdef
  set K := (Kth n A k 1)ᵀ with hKdef
  have hrank : K.rank = Module.finrank ℝ (eigA n A (-(mu : ℝ))) := by
    rw [hKdef, Matrix.rank_transpose]
    exact (KerFrame_rank_duval h ht htk hkn (LeftKer_roots htm)).1
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
  have hιinj : Function.Injective ι := by
    intro a b hab
    funext ⟨i, hi⟩
    have := congrFun hab i
    simpa [ι, hi] using this
  let φ := K.mulVecLin ∘ₗ ι
  have hsum := LinearMap.finrank_range_add_finrank_ker φ
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hsum
  have hr : Module.finrank ℝ (LinearMap.range φ) ≤ K.rank :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  let ψ : LinearMap.ker φ →ₗ[ℝ] leftKer n A k x :=
    { toFun := fun z => ⟨ι z.1, by
        refine ⟨?_, ?_⟩
        · show ∀ i ∈ Finset.univ \ outNbhd n A x, ι z.1 i = 0
          intro i hi
          rw [Finset.mem_sdiff] at hi
          have hiS : i ∉ S := hi.2
          show (if hi' : i ∈ S then z.1 ⟨i, hi'⟩ else 0) = 0
          simp [hiS]
        · exact LinearMap.mem_ker.2 (LinearMap.mem_ker.1 z.2)⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        simp
      map_smul' := by
        intro c a
        apply Subtype.ext
        simp }
  have hψ : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    apply hιinj
    exact congrArg (fun q : leftKer n A k x => q.1) hab
  have hle := LinearMap.finrank_le_finrank_of_injective hψ
  have hcard := LeftKer_card h x
  rw [← hSdef] at hcard
  have e1 : (S.card : ℤ) = (Module.finrank ℝ (LinearMap.range φ) : ℤ) +
      (Module.finrank ℝ (LinearMap.ker φ) : ℤ) := by exact_mod_cast hsum.symm
  have e2 : (Module.finrank ℝ (LinearMap.range φ) : ℤ) ≤
      (Module.finrank ℝ (eigA n A (-(mu : ℝ))) : ℤ) := by
    rw [← hrank]; exact_mod_cast hr
  have e3 : (Module.finrank ℝ (LinearMap.ker φ) : ℤ) ≤
      (Module.finrank ℝ (leftKer n A k x) : ℤ) := by exact_mod_cast hle
  omega

noncomputable def profSpace (n : Nat) (A : Mat) (k t : Int) (x : Fin n) :
    Submodule ℝ (Fin n → ℝ) where
  carrier := {f | (∀ i : Fin n, A x i ≠ 1 → f i = 0) ∧
    (∀ y z : Fin n, A x y = 1 → A x z = 1 → A y z = 1 → f y = f z) ∧
    (∑ y : Fin n, f y * ((k : ℝ) * (A y x : ℝ) - t) = 0) ∧
    (∀ z : Fin n, z ≠ x → A x z ≠ 1 → ∑ y : Fin n, f y * (2 * (A y z : ℝ) - A y x) = 0)}
  add_mem' := by
    rintro a b ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      simp [a1 i hi, b1 i hi]
    · intro y z hy hz hyz
      simp [a2 y z hy hz hyz, b2 y z hy hz hyz]
    · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, a3, b3, add_zero]
    · intro z hz hxz
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, a4 z hz hxz, b4 z hz hxz,
        add_zero]
  zero_mem' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i _
      rfl
    · intro y z _ _ _
      rfl
    · simp
    · intro z _ _
      simp
  smul_mem' := by
    rintro c a ⟨a1, a2, a3, a4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      simp [a1 i hi]
    · intro y z hy hz hyz
      simp [a2 y z hy hz hyz]
    · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, a3, mul_zero]
    · intro z hz hxz
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, a4 z hz hxz,
        mul_zero]

theorem LeftKer_bound (h : IsDSRG n A k t 1 mu) (ht : 0 < t) (htk : t < k) (hkn : k < (n : Int) - 1)
    (htm : t = 2 * mu) (x : Fin n) :
    k + 1 - (Module.finrank ℝ (eigA n A (-(mu : ℝ))) : ℤ) ≤
      (Module.finrank ℝ (profSpace n A k t x) : ℤ) := by
  classical
  have hn : 0 < n := by omega
  have hk : 0 < k := by omega
  have zo : ∀ i j : Fin n, A i j = 0 ∨ A i j = 1 := fun i j => h.1 i i.isLt j j.isLt
  have hxx : A x x = 0 := h.2.1 x x.isLt
  have hid : (mu : ℝ) * ((n : ℝ) - k + 1) = (k : ℝ) * ((k : ℝ) - 1) := by
    have e := k_sub_mul_k_sub h hn (LeftKer_roots htm)
    linear_combination -e
  have hk1 : (k : ℝ) - 1 ≠ 0 := by
    have : (1 : ℤ) < k := by omega
    have : (1 : ℝ) < k := by exact_mod_cast this
    linarith
  have hnk : (n : ℝ) - k + 1 ≠ 0 := by
    have : (k : ℝ) < (n : ℝ) - 1 := by exact_mod_cast hkn
    linarith
  have htR : (t : ℝ) = 2 * mu := by exact_mod_cast htm
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.id - (LinearMap.proj x).smulRight (Pi.single x (1 : ℝ))
  have hL : ∀ w : Fin n → ℝ, ∀ i : Fin n, L w i = w i - if i = x then w x else 0 := by
    intro w i
    by_cases e : i = x
    · subst e; simp [L]
    · simp [L, e]
  have hLsum : ∀ (w c : Fin n → ℝ), ∑ i : Fin n, L w i * c i = ∑ i : Fin n, w i * c i - w x * c x := by
    intro w c
    have e : ∀ i : Fin n, L w i * c i = w i * c i - (if i = x then w x * c x else 0) := by
      intro i
      rw [hL]
      by_cases ei : i = x
      · subst ei; simp
      · simp [ei]
    rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp
  have hmem : ∀ w ∈ leftKer n A k x, L w ∈ profSpace n A k t x := by
    intro w hw
    obtain ⟨ea, eb, ec, ed⟩ := LeftKer_eqs h hn hk hw
    have hzero : ∀ i : Fin n, i ≠ x → A x i ≠ 1 → w i = 0 := by
      intro i hi hxi
      apply (mem_vanishOn.1 hw.1) i
      rw [Finset.mem_sdiff, mem_outNbhd]
      exact ⟨Finset.mem_univ _, by rintro (e | e) <;> contradiction⟩
    have eb' : ∑ i : Fin n, w i * (A i x : ℝ) = 2 * w x := by
      rw [← eb]; apply Finset.sum_congr rfl; intro i _; ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [hL]
      by_cases e : i = x
      · subst e; simp
      · simp [e, hzero i e hi]
    · intro y z hy hz hyz
      have hyx : y ≠ x := by rintro rfl; rw [hxx] at hy; exact absurd hy (by decide)
      have hzx : z ≠ x := by rintro rfl; rw [hxx] at hz; exact absurd hz (by decide)
      rw [hL, hL]
      simp [hyx, hzx, ea y z hy hz hyz]
    · have e1 : ∀ i : Fin n, w i * ((k : ℝ) * (A i x : ℝ) - t) =
          (k : ℝ) * (w i * (A i x : ℝ)) - (t : ℝ) * w i := by intro i; ring
      rw [hLsum, Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, eb', hxx]
      have key : ((k : ℝ) - 1) * ((mu : ℝ) * ((∑ i : Fin n, w i) - w x) - (k : ℝ) * w x) = 0 := by
        linear_combination (mu : ℝ) * ed.symm + (w x) * hid
      have key2 : (mu : ℝ) * ((∑ i : Fin n, w i) - w x) - (k : ℝ) * w x = 0 := by
        rcases mul_eq_zero.1 key with e | e
        · exact absurd e hk1
        · exact e
      rw [htR]
      push_cast
      linear_combination (-2 : ℝ) * key2
    · intro z hz hxz
      have hxz0 : A x z = 0 := by rcases zo x z with e | e; exact e; exact absurd e hxz
      have e1 : ∀ i : Fin n, w i * (2 * (A i z : ℝ) - (A i x : ℝ)) =
          2 * ((A i z : ℝ) * w i) - w i * (A i x : ℝ) := by intro i; ring
      rw [hLsum, Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_sub_distrib,
        ← Finset.mul_sum, ec z hz hxz, eb', hxz0, hxx]
      push_cast
      ring
  let Ψ : leftKer n A k x →ₗ[ℝ] profSpace n A k t x :=
    { toFun := fun w => ⟨L w.1, hmem w.1 w.2⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        simp
      map_smul' := by
        intro c a
        apply Subtype.ext
        simp }
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw0
    have hLw : L w.1 = 0 := congrArg (fun q : profSpace n A k t x => q.1) hw0
    have hoff : ∀ i : Fin n, i ≠ x → w.1 i = 0 := by
      intro i hi
      have := congrFun hLw i
      rw [hL] at this
      simpa [hi] using this
    have hsumw : ∑ i : Fin n, w.1 i = w.1 x := by
      rw [Finset.sum_eq_single x]
      · intro i _ hi; exact hoff i hi
      · intro hx; exact absurd (Finset.mem_univ x) hx
    obtain ⟨_, _, _, ed⟩ := LeftKer_eqs h hn hk w.2
    rw [hsumw] at ed
    have hx0 : w.1 x = 0 := by
      have e : ((n : ℝ) - k + 1) * w.1 x = 0 := by linear_combination ed
      rcases mul_eq_zero.1 e with e' | e'
      · exact absurd e' hnk
      · exact e'
    apply Subtype.ext
    funext i
    by_cases hi : i = x
    · subst hi; simpa using hx0
    · simpa using hoff i hi
  have h1 := LeftKer_dim h ht htk hkn htm x
  have h2 : (Module.finrank ℝ (leftKer n A k x) : ℤ) ≤
      (Module.finrank ℝ (profSpace n A k t x) : ℤ) := by
    exact_mod_cast LinearMap.finrank_le_finrank_of_injective hΨ
  omega

theorem LeftKer_g (h : IsDSRG n A k t 1 mu) (ht : 0 < t) (htk : t < k) (hkn : k < (n : Int) - 1)
    (htm : t = 2 * mu) :
    (mu + 1) * (Module.finrank ℝ (eigA n A (-(mu : ℝ))) : ℤ) = k + n - 1 := by
  have hn : 0 < n := by omega
  have hμ : 0 < mu := by omega
  have hd : disc t 1 mu = (mu + 1) ^ 2 := by
    unfold disc
    rw [htm]
    ring
  have hpos : 0 < disc t 1 mu := by
    rw [hd]
    positivity
  have hc : Real.sqrt (disc t 1 mu : ℝ) = (mu : ℝ) + 1 := by
    rw [hd]
    push_cast
    exact Real.sqrt_sq (by positivity)
  have hrR : rR t 1 mu = 1 := by
    unfold rR
    rw [hc]
    push_cast
    ring
  have hsR : sR t 1 mu = -(mu : ℝ) := by
    unfold sR
    rw [hc]
    push_cast
    ring
  obtain ⟨_, _, hsum, htr⟩ := spectrum_counts h hn hpos hμ.ne'
  rw [hrR, hsR] at hsum htr
  set f := Module.finrank ℝ (eigA n A 1) with hf
  set g := Module.finrank ℝ (eigA n A (-(mu : ℝ))) with hg
  have hfg : (f : ℝ) + g = (n : ℝ) - 1 := by
    have : ((f + g : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) := by rw [hsum]
    push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne')] at this
    linarith
  have hgR : ((mu : ℝ) + 1) * g = k + n - 1 := by
    linarith
  exact_mod_cast hgR

theorem LeftKer_55_16_12_1_6 (A : Mat) (h : IsDSRG 55 A 16 12 1 6) (x : Fin 55) :
    7 ≤ Module.finrank ℝ (profSpace 55 A 16 12 x) := by
  have hb := LeftKer_bound h (by norm_num) (by norm_num) (by norm_num) (by norm_num) x
  have hg := LeftKer_g h (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  omega

end

end DsrgRank
