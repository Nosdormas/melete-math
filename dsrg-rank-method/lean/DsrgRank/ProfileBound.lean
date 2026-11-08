module

public import DsrgRank.LeftKernel

/-!
For lambda = 1 and t = 2 mu, proves counting identities for functions that are constant on the out-
arcs of a vertex (ArcConst) and the resulting bounds on their profiles, which the left-kernel lemmas
use.
-/

@[expose] public section

set_option autoImplicit false

namespace DsrgRank

open Matrix

section

variable {n : Nat} {A : Mat} {k t mu : Int}

def ArcConst (n : Nat) (A : Mat) (x : Fin n) (f : Fin n → ℝ) : Prop :=
  (∀ i : Fin n, A x i ≠ 1 → f i = 0) ∧
  (∀ y z : Fin n, A x y = 1 → A x z = 1 → A y z = 1 → f y = f z)

theorem ProfBound_in (h : IsDSRG n A k t 1 mu) {x : Fin n} {f : Fin n → ℝ}
    (hf : ArcConst n A x f) {w : Fin n} (hxw : A x w = 1) :
    ∑ y : Fin n, (A y w : ℝ) * f y = f w := by
  classical
  have zo : ∀ i j : Fin n, A i j = 0 ∨ A i j = 1 := fun i j => h.1 i i.isLt j j.isLt
  have e1 : ∀ y : Fin n, (A y w : ℝ) * f y = ((A x y : ℝ) * (A y w : ℝ)) * f w := by
    intro y
    rcases zo x y with e | e
    · rw [hf.1 y (by rw [e]; decide), e]
      simp
    · rcases zo y w with e' | e'
      · simp [e, e']
      · rw [hf.2 y w e hxw e']
        simp [e, e']
  rw [Finset.sum_congr rfl (fun y _ => e1 y), ← Finset.sum_mul, LeftKer_lam h hxw, one_mul]

theorem ProfBound_two (h : IsDSRG n A k t 1 mu) {x y : Fin n} (hxy : A x y = 1) :
    ∑ z : Fin n, (A y z : ℝ) * (A z x : ℝ) = (A y x : ℝ) + (mu : ℝ) * (1 - (A y x : ℝ)) := by
  have hne : (y : Nat) ≠ x := by
    intro e
    have : y = x := Fin.ext e
    subst this
    rw [h.2.1 y y.isLt] at hxy
    exact absurd hxy (by decide)
  have e := h.2.2.2.2 y y.isLt x x.isLt
  rw [sumBelow_eq_fin] at e
  simp only [delta, hne, ite_false] at e
  have eR := congrArg (fun q : ℤ => (q : ℝ)) e
  push_cast at eR
  rw [eR]
  ring

theorem ProfBound_cardP (h : IsDSRG n A k t 1 mu) (x : Fin n) :
    ∑ z : Fin n, (A z x : ℝ) * (1 - (A x z : ℝ)) = (k : ℝ) - t := by
  have hcol := h.2.2.2.1 x x.isLt
  rw [sumBelow_eq_fin] at hcol
  have hcolR : ∑ z : Fin n, (A z x : ℝ) = k := by exact_mod_cast hcol
  have e := h.2.2.2.2 x x.isLt x x.isLt
  rw [sumBelow_eq_fin] at e
  simp only [delta, ite_true, h.2.1 x x.isLt] at e
  have eR := congrArg (fun q : ℤ => (q : ℝ)) e
  push_cast at eR
  have hxx : ∑ z : Fin n, (A x z : ℝ) * (A z x : ℝ) = t := by rw [eR]; ring
  have split : ∀ z : Fin n, (A z x : ℝ) * (1 - (A x z : ℝ)) =
      (A z x : ℝ) - (A x z : ℝ) * (A z x : ℝ) := fun z => by ring
  rw [Finset.sum_congr rfl (fun z _ => split z), Finset.sum_sub_distrib, hcolR, hxx]

theorem ProfBound_P (h : IsDSRG n A k t 1 mu) {x : Fin n} {f : Fin n → ℝ}
    (hf : ArcConst n A x f) :
    ∑ z : Fin n, ((A z x : ℝ) * (1 - (A x z : ℝ))) * ∑ y : Fin n, (A y z : ℝ) * f y =
      (mu : ℝ) * ∑ y : Fin n, f y * (1 - (A y x : ℝ)) := by
  classical
  have zo : ∀ i j : Fin n, A i j = 0 ∨ A i j = 1 := fun i j => h.1 i i.isLt j j.isLt
  have s2 : ∀ z : Fin n, ((A z x : ℝ) * (A x z : ℝ)) * ∑ y : Fin n, (A y z : ℝ) * f y =
      (A z x : ℝ) * f z := by
    intro z
    rcases zo x z with e | e
    · rw [hf.1 z (by rw [e]; decide), e]
      simp
    · rw [ProfBound_in h hf e, e]
      simp
  have s3 : ∀ y : Fin n, f y * ∑ z : Fin n, (A y z : ℝ) * (A z x : ℝ) =
      f y * ((A y x : ℝ) + (mu : ℝ) * (1 - (A y x : ℝ))) := by
    intro y
    rcases zo x y with e | e
    · rw [hf.1 y (by rw [e]; decide)]
      simp
    · rw [ProfBound_two h e]
  have swap : ∑ z : Fin n, (A z x : ℝ) * ∑ y : Fin n, (A y z : ℝ) * f y =
      ∑ y : Fin n, f y * ∑ z : Fin n, (A y z : ℝ) * (A z x : ℝ) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    ring
  have split : ∀ z : Fin n, ((A z x : ℝ) * (1 - (A x z : ℝ))) * ∑ y : Fin n, (A y z : ℝ) * f y =
      (A z x : ℝ) * (∑ y : Fin n, (A y z : ℝ) * f y) -
        ((A z x : ℝ) * (A x z : ℝ)) * ∑ y : Fin n, (A y z : ℝ) * f y := fun z => by ring
  rw [Finset.sum_congr rfl (fun z _ => split z), Finset.sum_sub_distrib, swap,
    Finset.sum_congr rfl (fun z _ => s2 z), Finset.sum_congr rfl (fun y _ => s3 y)]
  have e4 : ∑ y : Fin n, f y * ((A y x : ℝ) + (mu : ℝ) * (1 - (A y x : ℝ))) =
      ∑ y : Fin n, (A y x : ℝ) * f y + (mu : ℝ) * ∑ y : Fin n, f y * (1 - (A y x : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [e4]
  ring

theorem ProfBound_sumO (h : IsDSRG n A k t 1 mu) {x : Fin n} {f : Fin n → ℝ}
    (hf : ArcConst n A x f) : ∑ z : Fin n, (A x z : ℝ) * f z = ∑ z : Fin n, f z := by
  have zo : ∀ i j : Fin n, A i j = 0 ∨ A i j = 1 := fun i j => h.1 i i.isLt j j.isLt
  apply Finset.sum_congr rfl
  intro z _
  rcases zo x z with e | e
  · rw [hf.1 z (by rw [e]; decide), e]
    simp
  · rw [e]
    simp

theorem ProfBound_out (h : IsDSRG n A k t 1 mu) {x : Fin n} {f : Fin n → ℝ}
    (hf : ArcConst n A x f) :
    ∑ z : Fin n, ((1 - (if z = x then (1 : ℝ) else 0)) * (1 - (A x z : ℝ))) *
        ∑ y : Fin n, (A y z : ℝ) * f y =
      ((k : ℝ) - 1) * ∑ y : Fin n, f y - ∑ y : Fin n, (A y x : ℝ) * f y := by
  classical
  have zo : ∀ i j : Fin n, A i j = 0 ∨ A i j = 1 := fun i j => h.1 i i.isLt j j.isLt
  have hxx : A x x = 0 := h.2.1 x x.isLt
  have wt : ∀ z : Fin n, (1 - (if z = x then (1 : ℝ) else 0)) * (1 - (A x z : ℝ)) =
      1 - (if z = x then (1 : ℝ) else 0) - (A x z : ℝ) := by
    intro z
    by_cases e : z = x
    · subst e
      simp [hxx]
    · simp [e]
  have hrow : ∀ y : Fin n, ∑ z : Fin n, (A y z : ℝ) = k := by
    intro y
    have e := h.2.2.1 y y.isLt
    rw [sumBelow_eq_fin] at e
    exact_mod_cast e
  have hall : ∑ z : Fin n, ∑ y : Fin n, (A y z : ℝ) * f y = (k : ℝ) * ∑ y : Fin n, f y := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Finset.sum_mul, hrow y, mul_comm]
  have hO : ∑ z : Fin n, (A x z : ℝ) * ∑ y : Fin n, (A y z : ℝ) * f y = ∑ y : Fin n, f y := by
    rw [← ProfBound_sumO h hf]
    apply Finset.sum_congr rfl
    intro z _
    rcases zo x z with e | e
    · rw [e]
      simp
    · rw [ProfBound_in h hf e]
  have term : ∀ z : Fin n, ((1 - (if z = x then (1 : ℝ) else 0)) * (1 - (A x z : ℝ))) *
      ∑ y : Fin n, (A y z : ℝ) * f y =
        (∑ y : Fin n, (A y z : ℝ) * f y) -
          (if z = x then ∑ y : Fin n, (A y z : ℝ) * f y else 0) -
          (A x z : ℝ) * ∑ y : Fin n, (A y z : ℝ) * f y := by
    intro z
    rw [wt z]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun z _ => term z), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', hall, hO]
  simp
  ring

theorem ProfBound_F (h : IsDSRG n A k t 1 mu) {x : Fin n} {f : Fin n → ℝ}
    (hf : ArcConst n A x f) :
    ∑ z : Fin n, ((1 - (if z = x then (1 : ℝ) else 0)) * (1 - (A x z : ℝ)) * (1 - (A z x : ℝ))) *
        ∑ y : Fin n, (A y z : ℝ) * f y =
      ((k : ℝ) - 1 - mu) * ∑ y : Fin n, f y + ((mu : ℝ) - 1) * ∑ y : Fin n, (A y x : ℝ) * f y := by
  classical
  have hxx : A x x = 0 := h.2.1 x x.isLt
  have wt : ∀ z : Fin n, ((1 - (if z = x then (1 : ℝ) else 0)) * (1 - (A x z : ℝ)) *
      (1 - (A z x : ℝ))) * ∑ y : Fin n, (A y z : ℝ) * f y =
        ((1 - (if z = x then (1 : ℝ) else 0)) * (1 - (A x z : ℝ))) *
            ∑ y : Fin n, (A y z : ℝ) * f y -
          ((A z x : ℝ) * (1 - (A x z : ℝ))) * ∑ y : Fin n, (A y z : ℝ) * f y := by
    intro z
    by_cases e : z = x
    · subst e
      simp [hxx]
    · simp [e]
      ring
  rw [Finset.sum_congr rfl (fun z _ => wt z), Finset.sum_sub_distrib, ProfBound_out h hf, ProfBound_P h hf]
  have e5 : ∑ y : Fin n, f y * (1 - (A y x : ℝ)) =
      ∑ y : Fin n, f y - ∑ y : Fin n, (A y x : ℝ) * f y := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [e5]
  ring

theorem LeftKer_colsum (h : IsDSRG n A k t 1 mu) (hn : 0 < n) (htm : t = 2 * mu) {x : Fin n}
    {f : Fin n → ℝ} (hf : ArcConst n A x f) :
    (mu : ℝ) * ∑ z : Fin n, ((1 - (if z = x then (1 : ℝ) else 0)) * (1 - (A x z : ℝ))) *
        ∑ y : Fin n, f y * (2 * (A y z : ℝ) - (A y x : ℝ)) =
      -((k : ℝ) - 1) * ∑ y : Fin n, f y * ((k : ℝ) * (A y x : ℝ) - t) := by
  classical
  have hxx : A x x = 0 := h.2.1 x x.isLt
  have hrowx := h.2.2.1 x x.isLt
  rw [sumBelow_eq_fin] at hrowx
  have hrowxR : ∑ z : Fin n, (A x z : ℝ) = k := by exact_mod_cast hrowx
  have hcnt : ∑ z : Fin n, (1 - (if z = x then (1 : ℝ) else 0)) * (1 - (A x z : ℝ)) =
      (n : ℝ) - 1 - k := by
    have wt : ∀ z : Fin n, (1 - (if z = x then (1 : ℝ) else 0)) * (1 - (A x z : ℝ)) =
        1 - (if z = x then (1 : ℝ) else 0) - (A x z : ℝ) := by
      intro z
      by_cases e : z = x
      · subst e
        simp [hxx]
      · simp [e]
    rw [Finset.sum_congr rfl (fun z _ => wt z), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', hrowxR]
    simp
  have split : ∀ z : Fin n, ((1 - (if z = x then (1 : ℝ) else 0)) * (1 - (A x z : ℝ))) *
      ∑ y : Fin n, f y * (2 * (A y z : ℝ) - (A y x : ℝ)) =
        2 * (((1 - (if z = x then (1 : ℝ) else 0)) * (1 - (A x z : ℝ))) *
          ∑ y : Fin n, (A y z : ℝ) * f y) -
        ((1 - (if z = x then (1 : ℝ) else 0)) * (1 - (A x z : ℝ))) *
          ∑ y : Fin n, (A y x : ℝ) * f y := by
    intro z
    have e1 : ∑ y : Fin n, f y * (2 * (A y z : ℝ) - (A y x : ℝ)) =
        2 * ∑ y : Fin n, (A y z : ℝ) * f y - ∑ y : Fin n, (A y x : ℝ) * f y := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _
      ring
    rw [e1]
    ring
  rw [Finset.sum_congr rfl (fun z _ => split z), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, ProfBound_out h hf, hcnt]
  have hk := k_sq h hn
  have hd : ∑ y : Fin n, f y * ((k : ℝ) * (A y x : ℝ) - t) =
      (k : ℝ) * ∑ y : Fin n, (A y x : ℝ) * f y - (t : ℝ) * ∑ y : Fin n, f y := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hd]
  have htR : (t : ℝ) = 2 * (mu : ℝ) := by exact_mod_cast htm
  rw [htR] at hk ⊢
  linear_combination (∑ y : Fin n, (A y x : ℝ) * f y) * hk

theorem LeftKer_gamma (h : IsDSRG n A k t 1 mu) (hn : 0 < n) (htm : t = 2 * mu) (hμ : 0 < mu)
    {x : Fin n} {f : Fin n → ℝ} (hf : ArcConst n A x f)
    (hd : ∑ y : Fin n, f y * ((k : ℝ) * (A y x : ℝ) - t) ≠ 0) (γ : Fin n → ℝ)
    (hγ : ∀ z : Fin n, z ≠ x → A x z ≠ 1 →
      ∑ y : Fin n, f y * (2 * (A y z : ℝ) - (A y x : ℝ)) =
        γ z * ∑ y : Fin n, f y * ((k : ℝ) * (A y x : ℝ) - t)) :
    ∑ z : Fin n, ((1 - (if z = x then (1 : ℝ) else 0)) * (1 - (A x z : ℝ))) * γ z =
      -((k : ℝ) - 1) / mu := by
  classical
  have zo : ∀ i j : Fin n, A i j = 0 ∨ A i j = 1 := fun i j => h.1 i i.isLt j j.isLt
  set D := ∑ y : Fin n, f y * ((k : ℝ) * (A y x : ℝ) - t) with hD
  have hc := LeftKer_colsum h hn htm hf
  have sub : ∀ z : Fin n, ((1 - (if z = x then (1 : ℝ) else 0)) * (1 - (A x z : ℝ))) *
      ∑ y : Fin n, f y * (2 * (A y z : ℝ) - (A y x : ℝ)) =
        (((1 - (if z = x then (1 : ℝ) else 0)) * (1 - (A x z : ℝ))) * γ z) * D := by
    intro z
    by_cases e : z = x
    · subst e
      simp
    · rcases zo x z with e' | e'
      · rw [hγ z e (by rw [e']; decide)]
        ring
      · rw [e']
        simp
  rw [Finset.sum_congr rfl (fun z _ => sub z), ← Finset.sum_mul] at hc
  have hμR : (mu : ℝ) ≠ 0 := by exact_mod_cast hμ.ne'
  field_simp
  have := mul_right_cancel₀ hd (show ((mu : ℝ) * ∑ z : Fin n,
      ((1 - (if z = x then (1 : ℝ) else 0)) * (1 - (A x z : ℝ))) * γ z) * D =
      (-((k : ℝ) - 1)) * D by rw [← hc]; ring)
  linarith

end

end DsrgRank
