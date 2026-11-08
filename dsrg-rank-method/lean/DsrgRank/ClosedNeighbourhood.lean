module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import DsrgRank.Spectral

/-!
For lambda = 0 proves that the closed neighbourhood of a vertex x, the vertex with its in- and out-
neighbours, has 2k - t + 1 vertices and that this number is at most the rank of A - theta I. For t =
2 mu + 1 this gives an inequality that excludes ten parameter sets, among them (50, 11, 7, 0, 3),
(68, 13, 7, 0, 3), (100, 16, 7, 0, 3) and (108, 19, 9, 0, 4).
-/

@[expose] public section

set_option autoImplicit false

namespace DsrgRank

open Matrix

section

variable {n : Nat} {A : Mat} {k t mu : Int}

theorem ClosedNbhd_no_tt (h : IsDSRG n A k t 0 mu) {a b c : Nat} (ha : a < n) (hb : b < n) (hc : c < n)
    (hab : A a b = 1) (hbc : A b c = 1) : A a c = 0 := by
  rcases h.1 a ha c hc with e | e
  · exact e
  · exfalso
    have hne : a ≠ c := by
      rintro rfl
      rw [h.2.1 a ha] at e
      exact absurd e (by decide)
    have eq := h.2.2.2.2 a ha c hc
    rw [show delta a c = 0 by simp [delta, hne], e] at eq
    have hge : sumBelow n (fun l => if l = b then (1 : Int) else 0) ≤
        sumBelow n (fun l => A a l * A l c) := by
      apply sumBelow_le
      intro l hl
      by_cases e' : l = b
      · subst e'
        simp [hab, hbc]
      · have e0 : (if l = b then (1 : Int) else 0) = 0 := by simp [e']
        rw [e0]
        exact (pair_facts (h.1 a ha l hl) (h.1 l hl c hc)).1
    rw [sumBelow_single 1 hb, eq] at hge
    norm_num at hge

theorem ClosedNbhd_rowZ (h : IsDSRG n A k t 0 mu) (i : Fin n) : ∑ j : Fin n, A i j = k := by
  have hi := h.2.2.1 i i.isLt
  rwa [sumBelow_eq_fin] at hi

theorem ClosedNbhd_colZ (h : IsDSRG n A k t 0 mu) (j : Fin n) : ∑ i : Fin n, A i j = k := by
  have hj := h.2.2.2.1 j j.isLt
  rwa [sumBelow_eq_fin] at hj

theorem ClosedNbhd_ttZ (h : IsDSRG n A k t 0 mu) (x : Fin n) : ∑ l : Fin n, A x l * A l x = t := by
  have e := h.2.2.2.2 x x.isLt x x.isLt
  rw [sumBelow_eq_fin, h.2.1 x x.isLt] at e
  simpa [delta] using e

theorem ClosedNbhd_muZ (h : IsDSRG n A k t 0 mu) {i x : Fin n} (hne : i ≠ x) (hix : A i x = 0) :
    ∑ l : Fin n, A i l * A l x = mu := by
  have e := h.2.2.2.2 i i.isLt x x.isLt
  have hne' : (i : Nat) ≠ x := Fin.val_ne_iff.mpr hne
  rw [sumBelow_eq_fin, hix] at e
  simpa [delta, hne'] using e

theorem ClosedNbhd_t_le_k (h : IsDSRG n A k t 0 mu) (x : Fin n) : t ≤ k := by
  rw [← ClosedNbhd_ttZ h x, ← ClosedNbhd_rowZ h x]
  apply Finset.sum_le_sum
  intro l _
  exact (pair_facts (h.1 x x.isLt l l.isLt) (h.1 l l.isLt x x.isLt)).2.1

theorem ClosedNbhd_rowEq (θ : ℝ) (u : Fin n → ℝ) (i : Fin n) :
    ((toR n A - θ • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u) i =
      (∑ j : Fin n, (A i j : ℝ) * u j) - θ * u i := by
  have e1 : (toR n A *ᵥ u) i = ∑ j : Fin n, (A i j : ℝ) * u j := by
    simp [Matrix.mulVec, dotProduct, toR]
  rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.smul_mulVec, Pi.smul_apply, Matrix.one_mulVec,
    smul_eq_mul, e1]

def nbhd (n : Nat) (A : Mat) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => i = x ∨ A x i = 1 ∨ A i x = 1)

theorem mem_nbhd {x i : Fin n} : i ∈ nbhd n A x ↔ (i = x ∨ A x i = 1 ∨ A i x = 1) := by
  simp [nbhd]

theorem ClosedNbhd_arcs (h : IsDSRG n A k t 0 mu) {x i j : Fin n} (hi : i ∈ nbhd n A x)
    (hj : j ∈ nbhd n A x) (hij : A i j = 1) :
    (i = x ∧ A x j = 1) ∨ (A i x = 1 ∧ j = x) ∨
      (A x i = 1 ∧ A i x = 0 ∧ A j x = 1 ∧ A x j = 0) := by
  have zo : ∀ a b : Fin n, A a b = 0 ∨ A a b = 1 := fun a b => h.1 a a.isLt b b.isLt
  have ntt : ∀ a b c : Fin n, A a b = 1 → A b c = 1 → A a c = 0 :=
    fun a b c hab hbc => ClosedNbhd_no_tt h a.isLt b.isLt c.isLt hab hbc
  rcases mem_nbhd.1 hi with ei | ei | ei
  · exact Or.inl ⟨ei, ei ▸ hij⟩
  · rcases mem_nbhd.1 hj with ej | ej | ej
    · exact Or.inr (Or.inl ⟨ej ▸ hij, ej⟩)
    · have e := ntt x i j ei hij
      rw [ej] at e
      exact absurd e (by decide)
    · refine Or.inr (Or.inr ⟨ei, ?_, ej, ntt x i j ei hij⟩)
      rcases zo i x with e | e
      · exact e
      · have e' := ntt i j x hij ej
        rw [e] at e'
        exact absurd e' (by decide)
  · rcases mem_nbhd.1 hj with ej | ej | ej
    · exact Or.inr (Or.inl ⟨ei, ej⟩)
    · have e := ntt i x j ei ej
      rw [hij] at e
      exact absurd e (by decide)
    · have e := ntt i j x hij ej
      rw [ei] at e
      exact absurd e (by decide)

theorem ClosedNbhd_kernel (h : IsDSRG n A k t 0 mu) (x : Fin n) {θ : ℝ} (hθ : θ ≠ 0)
    (hpoly : θ ^ 3 - (t : ℝ) * θ - (mu : ℝ) * ((k : ℝ) - t) ≠ 0) {u : Fin n → ℝ}
    (hsupp : ∀ i, i ∉ nbhd n A x → u i = 0)
    (hrow : ∀ i ∈ nbhd n A x, ((toR n A - θ • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u) i = 0) :
    u = 0 := by
  have zo : ∀ i j : Fin n, A i j = 0 ∨ A i j = 1 := fun i j => h.1 i i.isLt j j.isLt
  have ntt : ∀ a b c : Fin n, A a b = 1 → A b c = 1 → A a c = 0 :=
    fun a b c hab hbc => ClosedNbhd_no_tt h a.isLt b.isLt c.isLt hab hbc
  have hxx : A x x = 0 := h.2.1 x x.isLt
  have row : ∀ i ∈ nbhd n A x, ∑ j : Fin n, (A i j : ℝ) * u j = θ * u i := by
    intro i hi
    have e := hrow i hi
    rw [ClosedNbhd_rowEq] at e
    linarith
  have hin : ∀ i : Fin n, A i x = 1 → u i = u x / θ := by
    intro i hix
    have e := row i (mem_nbhd.2 (Or.inr (Or.inr hix)))
    have hsum : ∑ j : Fin n, (A i j : ℝ) * u j = u x := by
      rw [Finset.sum_eq_single x]
      · rw [hix]
        simp
      · intro j _ hjx
        by_cases hu : u j = 0
        · rw [hu, mul_zero]
        · have hj : j ∈ nbhd n A x := by
            by_contra hj
            exact hu (hsupp j hj)
          rcases mem_nbhd.1 hj with e1 | e1 | e1
          · exact absurd e1 hjx
          · rw [ntt i x j hix e1]
            simp
          · rcases zo i j with e2 | e2
            · rw [e2]
              simp
            · have e3 := ntt i j x e2 e1
              rw [hix] at e3
              exact absurd e3 (by decide)
      · intro hx
        exact absurd (Finset.mem_univ x) hx
    rw [hsum] at e
    rw [eq_div_iff hθ]
    linear_combination -e
  have hQ : ∀ i : Fin n, A x i = 1 → A i x = 0 → u i = mu * u x / θ ^ 2 := by
    intro i hxi hix
    have e := row i (mem_nbhd.2 (Or.inr (Or.inl hxi)))
    have hne : i ≠ x := by
      rintro rfl
      rw [hxx] at hxi
      exact absurd hxi (by decide)
    have hterm : ∀ j : Fin n, (A i j : ℝ) * u j = (A i j : ℝ) * A j x * (u x / θ) := by
      intro j
      rcases zo i j with e1 | e1
      · rw [e1]
        simp
      · rcases zo j x with e2 | e2
        · have hjx : j ≠ x := by
            rintro rfl
            rw [hix] at e1
            exact absurd e1 (by decide)
          have hxj : A x j = 0 := ntt x i j hxi e1
          have hj : j ∉ nbhd n A x := by
            rw [mem_nbhd]
            rintro (h1 | h1 | h1)
            · exact hjx h1
            · rw [hxj] at h1
              exact absurd h1 (by decide)
            · rw [e2] at h1
              exact absurd h1 (by decide)
          rw [hsupp j hj, e2]
          simp
        · rw [hin j e2, e1, e2]
          simp
    have hmu : ∑ j : Fin n, (A i j : ℝ) * A j x = mu := by
      exact_mod_cast ClosedNbhd_muZ h hne hix
    have hsum : ∑ j : Fin n, (A i j : ℝ) * u j = mu * (u x / θ) := by
      rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_mul, hmu]
    rw [hsum] at e
    have e' : (mu : ℝ) * u x = θ * (θ * u i) := by
      rw [← e]
      field_simp
    rw [eq_div_iff (pow_ne_zero 2 hθ)]
    linear_combination -e'
  have hx : u x = 0 := by
    have e := row x (mem_nbhd.2 (Or.inl rfl))
    have hterm : ∀ j : Fin n, (A x j : ℝ) * u j =
        (A x j : ℝ) * A j x * (u x / θ) +
          ((A x j : ℝ) - A x j * A j x) * (mu * u x / θ ^ 2) := by
      intro j
      rcases zo x j with e1 | e1
      · rw [e1]
        simp
      · rcases zo j x with e2 | e2
        · rw [hQ j e1 e2, e1, e2]
          simp
        · rw [hin j e2, e1, e2]
          simp
    have hk : ∑ j : Fin n, (A x j : ℝ) = k := by exact_mod_cast ClosedNbhd_rowZ h x
    have ht : ∑ j : Fin n, (A x j : ℝ) * A j x = t := by exact_mod_cast ClosedNbhd_ttZ h x
    have hsum : ∑ j : Fin n, (A x j : ℝ) * u j = t * (u x / θ) + (k - t) * (mu * u x / θ ^ 2) := by
      rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, ← Finset.sum_mul,
        ← Finset.sum_mul, Finset.sum_sub_distrib, hk, ht]
    rw [hsum] at e
    have e' : (t : ℝ) * θ * u x + ((k : ℝ) - t) * mu * u x = θ ^ 3 * u x := by
      calc (t : ℝ) * θ * u x + ((k : ℝ) - t) * mu * u x
          = θ ^ 2 * (t * (u x / θ) + (k - t) * (mu * u x / θ ^ 2)) := by
            field_simp
          _ = θ ^ 2 * (θ * u x) := by rw [e]
          _ = θ ^ 3 * u x := by ring
    have e2 : u x * (θ ^ 3 - (t : ℝ) * θ - (mu : ℝ) * ((k : ℝ) - t)) = 0 := by
      linear_combination -e'
    exact (mul_eq_zero.1 e2).resolve_right hpoly
  funext i
  show u i = 0
  by_cases hi : i ∈ nbhd n A x
  · rcases mem_nbhd.1 hi with e1 | e1 | e1
    · rw [e1, hx]
    · rcases zo i x with e2 | e2
      · rw [hQ i e1 e2, hx]
        simp
      · rw [hin i e2, hx]
        simp
    · rw [hin i e1, hx]
      simp
  · exact hsupp i hi

theorem ClosedNbhd_rank (h : IsDSRG n A k t 0 mu) (x : Fin n) {θ : ℝ} (hθ : θ ≠ 0)
    (hpoly : θ ^ 3 - (t : ℝ) * θ - (mu : ℝ) * ((k : ℝ) - t) ≠ 0) :
    (nbhd n A x).card ≤ (toR n A - θ • (1 : Matrix (Fin n) (Fin n) ℝ)).rank := by
  classical
  set S := nbhd n A x with hSdef
  set M := toR n A - θ • (1 : Matrix (Fin n) (Fin n) ℝ) with hMdef
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
  have hinj : Function.Injective (M.mulVecLin ∘ₗ ι) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hu : ι z = 0 := by
      apply ClosedNbhd_kernel h x hθ hpoly
      · intro i hi
        have hi' : i ∉ S := by
          rw [hSdef]
          exact hi
        show (if hi'' : i ∈ S then z ⟨i, hi''⟩ else 0) = 0
        simp [hi']
      · intro i _
        have := congrFun hz i
        rw [LinearMap.comp_apply, Matrix.mulVecLin_apply] at this
        exact this
    funext ⟨i, hi⟩
    have := congrFun hu i
    simpa [ι, hi] using this
  have h1 : Module.finrank ℝ (LinearMap.range (M.mulVecLin ∘ₗ ι)) = S.card := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe]
  have h2 : LinearMap.range (M.mulVecLin ∘ₗ ι) ≤ LinearMap.range M.mulVecLin :=
    LinearMap.range_comp_le_range _ _
  have h3 := Submodule.finrank_mono h2
  rw [h1] at h3
  exact h3

/-- `|N[x]| = 2k − t + 1`. -/
theorem ClosedNbhd_card (h : IsDSRG n A k t 0 mu) (x : Fin n) :
    ((nbhd n A x).card : ℤ) = 2 * k - t + 1 := by
  classical
  have zo : ∀ i j : Fin n, A i j = 0 ∨ A i j = 1 := fun i j => h.1 i i.isLt j j.isLt
  have hxx : A x x = 0 := h.2.1 x x.isLt
  have hterm : ∀ i : Fin n, (if (i = x ∨ A x i = 1 ∨ A i x = 1) then (1 : ℤ) else 0) =
      ((if i = x then 1 else 0) + A x i + A i x - A x i * A i x) := by
    intro i
    by_cases hi : i = x
    · subst hi
      simp [hxx]
    · rcases zo x i with e1 | e1 <;> rcases zo i x with e2 | e2 <;> simp [hi, e1, e2]
  have hc : ((nbhd n A x).card : ℤ) =
      ∑ i : Fin n, (if (i = x ∨ A x i = 1 ∨ A i x = 1) then (1 : ℤ) else 0) := by
    rw [nbhd, Finset.card_filter]
    push_cast
    rfl
  rw [hc, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, ClosedNbhd_rowZ h x, ClosedNbhd_colZ h x, ClosedNbhd_ttZ h x]
  simp
  ring

theorem ClosedNbhd_bound (h : IsDSRG n A k t 0 mu) (hn : 0 < n) (hpos : 0 < disc t 0 mu) (hμ : mu ≠ 0)
    {θ θ' : ℝ} (hr : IsRootPair t 0 mu θ θ') (hθ : θ ≠ 0)
    (hpoly : θ ^ 3 - (t : ℝ) * θ - (mu : ℝ) * ((k : ℝ) - t) ≠ 0) :
    2 * k - t ≤ (Module.finrank ℝ (eigA n A θ') : ℤ) := by
  have h1 := ClosedNbhd_rank h ⟨0, hn⟩ hθ hpoly
  rw [rank_sub_root h hn hpos hμ hr] at h1
  have h2 := ClosedNbhd_card h ⟨0, hn⟩
  have h3 : ((nbhd n A ⟨0, hn⟩).card : ℤ) ≤ 1 + (Module.finrank ℝ (eigA n A θ') : ℤ) := by
    exact_mod_cast h1
  omega

theorem ClosedNbhd_r_one (h : IsDSRG n A k t 0 mu) (hn : 0 < n) (hμ : 0 < mu) (ht : t = 2 * mu + 1) :
    (2 * k - t) * (mu + 2) ≤ k + n - 1 := by
  have hd : disc t 0 mu = (mu + 2) ^ 2 := by
    unfold disc
    rw [ht]
    ring
  have hpos : 0 < disc t 0 mu := by
    rw [hd]
    positivity
  have hc : Real.sqrt (disc t 0 mu : ℝ) = (mu : ℝ) + 2 := by
    rw [hd]
    push_cast
    exact Real.sqrt_sq (by positivity)
  have hrR : rR t 0 mu = 1 := by
    unfold rR
    rw [hc]
    push_cast
    ring
  have hsR : sR t 0 mu = -((mu : ℝ) + 1) := by
    unfold sR
    rw [hc]
    push_cast
    ring
  obtain ⟨_, _, hsum, htr⟩ := spectrum_counts h hn hpos hμ.ne'
  rw [hrR, hsR] at hsum htr
  set f := Module.finrank ℝ (eigA n A 1) with hf
  set g := Module.finrank ℝ (eigA n A (-((mu : ℝ) + 1))) with hg
  have hr : IsRootPair t 0 mu 1 (-((mu : ℝ) + 1)) := by
    refine ⟨?_, ?_⟩
    · push_cast
      ring
    · rw [ht]
      push_cast
      ring
  have htk := ClosedNbhd_t_le_k h ⟨0, hn⟩
  have hpoly : (1 : ℝ) ^ 3 - (t : ℝ) * 1 - (mu : ℝ) * ((k : ℝ) - t) ≠ 0 := by
    have hkt : (0 : ℝ) ≤ (k : ℝ) - t := by
      have : (t : ℝ) ≤ k := by exact_mod_cast htk
      linarith
    have hm : (0 : ℝ) < mu := by exact_mod_cast hμ
    have htR : (t : ℝ) = 2 * mu + 1 := by exact_mod_cast ht
    have : (0 : ℝ) ≤ (mu : ℝ) * ((k : ℝ) - t) := mul_nonneg hm.le hkt
    rw [htR]
    nlinarith
  have hb := ClosedNbhd_bound h hn hpos hμ.ne' hr one_ne_zero hpoly
  have hfg : (f : ℝ) + g = (n : ℝ) - 1 := by
    have : ((f + g : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) := by rw [hsum]
    push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne')] at this
    linarith
  have hgR : ((mu : ℝ) + 2) * g = k + n - 1 := by
    linarith
  have hgZ : (mu + 2) * (g : ℤ) = k + n - 1 := by
    exact_mod_cast hgR
  have hm2 : (0 : ℤ) ≤ mu + 2 := by omega
  nlinarith [mul_le_mul_of_nonneg_left hb hm2]

theorem ClosedNbhd_no_50_11_7_0_3 (A : Mat) : ¬ IsDSRG 50 A 11 7 0 3 := by
  intro h
  have := ClosedNbhd_r_one h (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

theorem ClosedNbhd_no_68_13_7_0_3 (A : Mat) : ¬ IsDSRG 68 A 13 7 0 3 := by
  intro h
  have := ClosedNbhd_r_one h (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

theorem ClosedNbhd_no_100_16_7_0_3 (A : Mat) : ¬ IsDSRG 100 A 16 7 0 3 := by
  intro h
  have := ClosedNbhd_r_one h (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

theorem ClosedNbhd_no_108_19_9_0_4 (A : Mat) : ¬ IsDSRG 108 A 19 9 0 4 := by
  intro h
  have := ClosedNbhd_r_one h (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

theorem ClosedNbhd_no_54_13_9_0_4 (A : Mat) : ¬ IsDSRG 54 A 13 9 0 4 := by
  intro h; have := ClosedNbhd_r_one h (by norm_num) (by norm_num) (by norm_num); norm_num at this

theorem ClosedNbhd_no_64_17_13_0_6 (A : Mat) : ¬ IsDSRG 64 A 17 13 0 6 := by
  intro h; have := ClosedNbhd_r_one h (by norm_num) (by norm_num) (by norm_num); norm_num at this

theorem ClosedNbhd_no_70_15_9_0_4 (A : Mat) : ¬ IsDSRG 70 A 15 9 0 4 := by
  intro h; have := ClosedNbhd_r_one h (by norm_num) (by norm_num) (by norm_num); norm_num at this

theorem ClosedNbhd_no_78_19_13_0_6 (A : Mat) : ¬ IsDSRG 78 A 19 13 0 6 := by
  intro h; have := ClosedNbhd_r_one h (by norm_num) (by norm_num) (by norm_num); norm_num at this

theorem ClosedNbhd_no_88_23_17_0_8 (A : Mat) : ¬ IsDSRG 88 A 23 17 0 8 := by
  intro h; have := ClosedNbhd_r_one h (by norm_num) (by norm_num) (by norm_num); norm_num at this

theorem ClosedNbhd_no_110_31_25_0_12 (A : Mat) : ¬ IsDSRG 110 A 31 25 0 12 := by
  intro h; have := ClosedNbhd_r_one h (by norm_num) (by norm_num) (by norm_num); norm_num at this

end

end DsrgRank
