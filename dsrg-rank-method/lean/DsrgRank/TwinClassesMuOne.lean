import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import DsrgRank.Spectral

set_option autoImplicit false

namespace DsrgRank

open Matrix

section

variable {n : Nat}

def outN (A : Mat) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j = x ∨ A x j = 1)

def inN (A : Mat) (y : Fin n) : Finset (Fin n) := outN (transpose A) y

def rowCl (A : Mat) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun y => outN A y = outN A x)

def colCl (A : Mat) (x : Fin n) : Finset (Fin n) := rowCl (transpose A) x

theorem mem_outN {A : Mat} {x j : Fin n} : j ∈ outN A x ↔ j = x ∨ A x j = 1 := by
  simp [outN]

theorem mem_inN {A : Mat} {y i : Fin n} : i ∈ inN A y ↔ i = y ∨ A i y = 1 := by
  rw [inN, mem_outN]
  exact Iff.rfl

theorem mem_rowCl {A : Mat} {x y : Fin n} : y ∈ rowCl A x ↔ outN A y = outN A x := by
  simp [rowCl]

theorem mem_colCl {A : Mat} {x y : Fin n} : y ∈ colCl A x ↔ inN A y = inN A x := by
  simp [colCl, rowCl, inN]

/-- `j ∈ N⁺[x] ⟺ x ∈ N⁻[j]`. -/
theorem out_iff_in {A : Mat} {x j : Fin n} : j ∈ outN A x ↔ x ∈ inN A j := by
  rw [mem_outN, mem_inN]
  constructor
  · rintro (e | e)
    · exact Or.inl e.symm
    · exact Or.inr e
  · rintro (e | e)
    · exact Or.inl e.symm
    · exact Or.inr e

theorem self_mem_outN {A : Mat} (x : Fin n) : x ∈ outN A x := mem_outN.2 (Or.inl rfl)

theorem self_mem_inN {A : Mat} (x : Fin n) : x ∈ inN A x := mem_inN.2 (Or.inl rfl)

theorem self_mem_rowCl {A : Mat} (x : Fin n) : x ∈ rowCl A x := mem_rowCl.2 rfl

theorem self_mem_colCl {A : Mat} (x : Fin n) : x ∈ colCl A x := mem_colCl.2 rfl

theorem rowCl_eq {A : Mat} {x y : Fin n} (hy : y ∈ rowCl A x) : rowCl A y = rowCl A x := by
  ext z
  rw [mem_rowCl, mem_rowCl, mem_rowCl.1 hy]

theorem colCl_eq {A : Mat} {x y : Fin n} (hy : y ∈ colCl A x) : colCl A y = colCl A x := by
  ext z
  rw [mem_colCl, mem_colCl, mem_colCl.1 hy]

theorem delta_comm (i j : Nat) : delta i j = delta j i := by
  unfold delta
  by_cases e : i = j
  · simp [e]
  · simp [e, Ne.symm e]

theorem isDSRG_transpose {A : Mat} {k t lam mu : Int} (h : IsDSRG n A k t lam mu) :
    IsDSRG n (transpose A) k t lam mu := by
  refine ⟨fun i hi j hj => h.1 j hj i hi, fun i hi => h.2.1 i hi, fun i hi => h.2.2.2.1 i hi,
    fun j hj => h.2.2.1 j hj, fun i hi j hj => ?_⟩
  have e := h.2.2.2.2 j hj i hi
  have e2 : sumBelow n (fun l => transpose A i l * transpose A l j) =
      sumBelow n (fun l => A j l * A l i) := by
    apply sumBelow_congr
    intro l _
    simp only [transpose]
    ring
  rw [e2, e, delta_comm j i]
  rfl

theorem sum_mul_delta (f : Fin n → Int) (y : Fin n) :
    ∑ l : Fin n, f l * delta l y = f y := by
  rw [Finset.sum_eq_single y]
  · simp [delta]
  · intro b _ hb
    have : (b : Nat) ≠ y := fun e => hb (Fin.ext e)
    simp [delta, this]
  · simp

theorem sum_delta_mulTw (f : Fin n → Int) (x : Fin n) :
    ∑ l : Fin n, delta x l * f l = f x := by
  rw [Finset.sum_eq_single x]
  · simp [delta]
  · intro b _ hb
    have : (x : Nat) ≠ b := fun e => hb (Fin.ext e.symm)
    simp [delta, this]
  · simp

theorem card_eq_sum (S : Finset (Fin n)) :
    (S.card : Int) = ∑ l : Fin n, if l ∈ S then (1 : Int) else 0 := by
  rw [Finset.sum_boole]
  simp

theorem TwinMuOne_ind {A : Mat} {k t lam mu : Int} (h : IsDSRG n A k t lam mu) (x l : Fin n) :
    (if l ∈ outN A x then (1 : Int) else 0) = A x l + delta x l := by
  by_cases hl : l = x
  · subst hl
    simp [mem_outN, delta, h.2.1 l l.isLt]
  · have hne : (x : Nat) ≠ l := fun e => hl (Fin.ext e.symm)
    rcases h.1 x x.isLt l l.isLt with e | e <;> simp [mem_outN, delta, hl, hne, e]

variable {A : Mat} {k t lam : Int}

/-- `|N⁺[x]| = k + 1`. -/
theorem TwinMuOne_card_out (h : IsDSRG n A k t lam 1) (x : Fin n) :
    ((outN A x).card : Int) = k + 1 := by
  have hd : ∑ l : Fin n, delta x l = 1 := by
    simpa using sum_delta_mulTw (fun _ => (1 : Int)) x
  rw [card_eq_sum, Finset.sum_congr rfl (fun l _ => TwinMuOne_ind h x l), Finset.sum_add_distrib, hd]
  have hk := h.2.2.1 x x.isLt
  rw [sumBelow_eq_fin] at hk
  rw [hk]

/-- `|N⁻[y]| = k + 1`. -/
theorem TwinMuOne_card_in (h : IsDSRG n A k t lam 1) (y : Fin n) :
    ((inN A y).card : Int) = k + 1 :=
  TwinMuOne_card_out (isDSRG_transpose h) y

theorem TwinMuOne_inter (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (x y : Fin n) :
    ((outN A x ∩ inN A y).card : Int) =
      (lam + 1) * (if y ∈ outN A x then 1 else 0) + 1 := by
  have hT := isDSRG_transpose h
  have e : ∀ l : Fin n, (if l ∈ outN A x ∩ inN A y then (1 : Int) else 0) =
      (A x l + delta x l) * (A l y + delta l y) := by
    intro l
    have e1 := TwinMuOne_ind h x l
    have e2 := TwinMuOne_ind hT y l
    simp only [transpose] at e2
    rw [delta_comm y l] at e2
    rw [← e1, ← e2]
    show (if l ∈ outN A x ∩ outN (transpose A) y then (1 : Int) else 0) = _
    by_cases h1 : l ∈ outN A x <;> by_cases h2 : l ∈ outN (transpose A) y <;>
      simp [Finset.mem_inter, h1, h2]
  rw [card_eq_sum, Finset.sum_congr rfl (fun l _ => e l), TwinMuOne_ind h x y]
  have h2 := h.2.2.2.2 x x.isLt y y.isLt
  rw [sumBelow_eq_fin] at h2
  have hexp : ∀ l : Fin n, (A x l + delta x l) * (A l y + delta l y) =
      A x l * A l y + A x l * delta l y + delta x l * A l y + delta x l * delta l y := by
    intro l
    ring
  rw [Finset.sum_congr rfl (fun l _ => hexp l), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, sum_mul_delta (fun l => A x l) y, sum_delta_mulTw (fun l => A l y) x,
    sum_delta_mulTw (fun l => delta l y) x, h2, ht]
  ring

theorem TwinMuOne_inter_out (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) {x y : Fin n}
    (hy : y ∉ outN A x) : (outN A x ∩ inN A y).card = 1 := by
  have e := TwinMuOne_inter h ht x y
  simp only [hy, ite_false, mul_zero, zero_add] at e
  exact_mod_cast e

theorem TwinMuOne_inter_in (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) {x y : Fin n}
    (hy : y ∈ outN A x) : ((outN A x ∩ inN A y).card : Int) = lam + 2 := by
  have e := TwinMuOne_inter h ht x y
  simp only [hy, ite_true, mul_one] at e
  rw [e]
  ring

theorem twin_out {x y : Fin n} (hy : y ∈ rowCl A x) : y ∈ outN A x := by
  rw [← mem_rowCl.1 hy]
  exact self_mem_outN y

theorem twin_in {x y : Fin n} (hy : y ∈ rowCl A x) : y ∈ inN A x := by
  rw [← out_iff_in, mem_rowCl.1 hy]
  exact self_mem_outN x

theorem rowCl_sub_out (x : Fin n) : rowCl A x ⊆ outN A x := fun _ hy => twin_out hy

theorem TwinMuOne_out_eq (h : IsDSRG n A k t lam 1) {x u : Fin n} (hsub : outN A x ⊆ outN A u) :
    outN A x = outN A u := by
  apply Finset.eq_of_subset_of_card_le hsub
  have e1 := TwinMuOne_card_out h x
  have e2 := TwinMuOne_card_out h u
  omega

theorem TwinMuOne_exists_out (h : IsDSRG n A k t lam 1) {x u : Fin n} (hne : outN A u ≠ outN A x) :
    ∃ w ∈ outN A u, w ∉ outN A x := by
  by_contra hc
  apply hne
  apply TwinMuOne_out_eq h
  intro w hw
  by_contra hwx
  exact hc ⟨w, hw, hwx⟩

theorem TwinMuOne_col_union {x y y' : Fin n} (hy : y ∈ outN A x) (hy' : y' ∈ colCl A y) :
    y' ∈ outN A x := by
  rw [out_iff_in, mem_colCl.1 hy']
  exact out_iff_in.1 hy

theorem colCl_sub (x : Fin n) : colCl A x ⊆ outN A x ∩ inN A x := by
  intro y hy
  refine Finset.mem_inter.2 ⟨TwinMuOne_col_union (self_mem_outN x) hy, ?_⟩
  rw [← mem_colCl.1 hy]
  exact self_mem_inN y

theorem TwinMuOne_double (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (htk : t < k) {x y : Fin n}
    (hr : y ∈ rowCl A x) (hc : y ∈ colCl A x) : y = x := by
  by_contra hyx
  have hro := mem_rowCl.1 hr
  have hco := mem_colCl.1 hc
  have hall : ∀ u ∈ inN A x, u ∈ outN A x := by
    intro u hu
    have hsub : outN A x ⊆ outN A u := by
      intro w hw
      by_contra hwu
      have h1 := TwinMuOne_inter_out h ht hwu
      have hx : x ∈ outN A u ∩ inN A w :=
        Finset.mem_inter.2 ⟨out_iff_in.2 hu, out_iff_in.1 hw⟩
      have hy : y ∈ outN A u ∩ inN A w := by
        refine Finset.mem_inter.2 ⟨out_iff_in.2 (by rw [hco]; exact hu), ?_⟩
        rw [← out_iff_in, hro]
        exact hw
      have := Finset.card_le_one.1 (le_of_eq h1) y hy x hx
      exact hyx this
    have heq := TwinMuOne_out_eq h hsub
    rw [heq]
    exact self_mem_outN u
  have hcard : outN A x ∩ inN A x = inN A x := by
    ext u
    simp only [Finset.mem_inter]
    exact ⟨fun hu => hu.2, fun hu => ⟨hall u hu, hu⟩⟩
  have e1 := TwinMuOne_inter_in h ht (self_mem_outN (A := A) x)
  rw [hcard, TwinMuOne_card_in h x] at e1
  omega

theorem TwinMuOne_ad (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (htk : t < k) (x : Fin n) :
    ((rowCl A x).card : Int) + (colCl A x).card ≤ lam + 3 := by
  have hsub : rowCl A x ∪ colCl A x ⊆ outN A x ∩ inN A x := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · exact Finset.mem_inter.2 ⟨twin_out hy, twin_in hy⟩
    · exact colCl_sub x hy
  have hint : (rowCl A x ∩ colCl A x).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro a ha b hb
    have ha' := Finset.mem_inter.1 ha
    have hb' := Finset.mem_inter.1 hb
    rw [TwinMuOne_double h ht htk ha'.1 ha'.2, TwinMuOne_double h ht htk hb'.1 hb'.2]
  have hu := Finset.card_union_add_card_inter (rowCl A x) (colCl A x)
  have hle := Finset.card_le_card hsub
  have e1 := TwinMuOne_inter_in h ht (self_mem_outN (A := A) x)
  omega

theorem TwinMuOne_unique (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) {x u u' : Fin n}
    (hu : u ∈ outN A x) (hux : u ∉ rowCl A x) (hu' : u' ∈ rowCl A u)
    (hu'x : u' ∈ outN A x) : u' = u := by
  have hne : outN A u ≠ outN A x := fun e => hux (mem_rowCl.2 e)
  obtain ⟨w, hwu, hwx⟩ := TwinMuOne_exists_out h hne
  have h1 := TwinMuOne_inter_out h ht hwx
  have m1 : u ∈ outN A x ∩ inN A w := Finset.mem_inter.2 ⟨hu, out_iff_in.1 hwu⟩
  have m2 : u' ∈ outN A x ∩ inN A w := by
    refine Finset.mem_inter.2 ⟨hu'x, ?_⟩
    rw [← out_iff_in, mem_rowCl.1 hu']
    exact hwu
  exact Finset.card_le_one.1 (le_of_eq h1) u' m2 u m1

theorem TwinMuOne_one (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) {x u : Fin n}
    (hux : u ∉ rowCl A x) : (outN A u ∩ rowCl A x).card ≤ 1 := by
  apply Finset.card_le_one.2
  intro y1 hy1 y2 hy2
  have a1 := Finset.mem_inter.1 hy1
  have a2 := Finset.mem_inter.1 hy2
  have hne : y1 ∉ rowCl A u := by
    intro e
    apply hux
    rw [mem_rowCl, ← mem_rowCl.1 a1.2]
    exact (mem_rowCl.1 e).symm
  have htw : y2 ∈ rowCl A y1 := by
    rw [mem_rowCl, mem_rowCl.1 a1.2, mem_rowCl.1 a2.2]
  exact (TwinMuOne_unique h ht a1.1 hne htw a2.1).symm

theorem TwinMuOne_class (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (htk : t < k) (x : Fin n) :
    ((rowCl A x).card : Int) * (lam + 2 - (rowCl A x).card) ≤
      k + 1 - (rowCl A x).card ∧ ((rowCl A x).card : Int) ≤ lam + 1 := by
  classical
  have hCN : rowCl A x ⊆ outN A x := rowCl_sub_out x
  have hCin : ∀ z ∈ outN A x, rowCl A x ⊆ inN A z := by
    intro z hz c hc
    rw [← out_iff_in, mem_rowCl.1 hc]
    exact hz
  have hNC : ((outN A x \ rowCl A x).card : Int) = k + 1 - (rowCl A x).card := by
    have e1 := Finset.card_sdiff_add_card_eq_card hCN
    have e2 := TwinMuOne_card_out h x
    omega
  have hY : ∀ y ∈ rowCl A x,
      ((((outN A x \ rowCl A x).filter (fun u => u ∈ inN A y)).card : Nat) : Int) =
        lam + 2 - (rowCl A x).card := by
    intro y hy
    have hyN : y ∈ outN A x := hCN hy
    have e1 := TwinMuOne_inter_in h ht hyN
    have hsplit : outN A x ∩ inN A y =
        rowCl A x ∪ (outN A x \ rowCl A x).filter (fun u => u ∈ inN A y) := by
      ext u
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hu : u ∈ rowCl A x
        · exact Or.inl hu
        · exact Or.inr ⟨⟨h1, hu⟩, h2⟩
      · rintro (hu | ⟨⟨h1, _⟩, h2⟩)
        · exact ⟨hCN hu, hCin y hyN hu⟩
        · exact ⟨h1, h2⟩
    have hdisj : Disjoint (rowCl A x)
        ((outN A x \ rowCl A x).filter (fun u => u ∈ inN A y)) := by
      rw [Finset.disjoint_left]
      intro u hu hu'
      exact (Finset.mem_sdiff.1 (Finset.mem_filter.1 hu').1).2 hu
    rw [hsplit, Finset.card_union_of_disjoint hdisj] at e1
    push_cast at e1
    omega
  have hswap : ∑ y ∈ rowCl A x,
      ((outN A x \ rowCl A x).filter (fun u => u ∈ inN A y)).card =
      ∑ u ∈ outN A x \ rowCl A x, ((rowCl A x).filter (fun y => u ∈ inN A y)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hle1 : ∀ u ∈ outN A x \ rowCl A x,
      ((rowCl A x).filter (fun y => u ∈ inN A y)).card ≤ 1 := by
    intro u hu
    have hux : u ∉ rowCl A x := (Finset.mem_sdiff.1 hu).2
    have hsub : (rowCl A x).filter (fun y => u ∈ inN A y) ⊆ outN A u ∩ rowCl A x := by
      intro y hy
      have hy' := Finset.mem_filter.1 hy
      exact Finset.mem_inter.2 ⟨out_iff_in.2 hy'.2, hy'.1⟩
    exact (Finset.card_le_card hsub).trans (TwinMuOne_one h ht hux)
  have hsumle : ∑ u ∈ outN A x \ rowCl A x,
      ((rowCl A x).filter (fun y => u ∈ inN A y)).card ≤ (outN A x \ rowCl A x).card := by
    calc ∑ u ∈ outN A x \ rowCl A x, ((rowCl A x).filter (fun y => u ∈ inN A y)).card
          ≤ ∑ _u ∈ outN A x \ rowCl A x, 1 := Finset.sum_le_sum hle1
      _ = (outN A x \ rowCl A x).card := by simp
  have hsumY : ((∑ y ∈ rowCl A x,
      ((outN A x \ rowCl A x).filter (fun u => u ∈ inN A y)).card : Nat) : Int) =
      (rowCl A x).card * (lam + 2 - (rowCl A x).card) := by
    push_cast
    rw [Finset.sum_congr rfl hY, Finset.sum_const, nsmul_eq_mul]
  refine ⟨?_, ?_⟩
  · have hc : ((∑ y ∈ rowCl A x,
        ((outN A x \ rowCl A x).filter (fun u => u ∈ inN A y)).card : Nat) : Int) ≤
        ((outN A x \ rowCl A x).card : Int) := by
      rw [hswap]
      exact_mod_cast hsumle
    rw [hsumY, hNC] at hc
    exact hc
  ·
    have hne : (outN A x \ rowCl A x).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hem
      have hNC' : outN A x ⊆ rowCl A x := Finset.sdiff_eq_empty_iff_subset.1 hem
      have hsub : outN A x ⊆ outN A x ∩ inN A x := by
        intro u hu
        exact Finset.mem_inter.2 ⟨hu, hCin x (self_mem_outN x) (hNC' hu)⟩
      have hle := Finset.card_le_card hsub
      have e1 := TwinMuOne_inter_in h ht (self_mem_outN (A := A) x)
      have e2 := TwinMuOne_card_out h x
      omega
    obtain ⟨z, hz⟩ := hne
    have hz' := Finset.mem_sdiff.1 hz
    have e1 := TwinMuOne_inter_in h ht hz'.1
    have hsub : insert z (rowCl A x) ⊆ outN A x ∩ inN A z := by
      intro u hu
      rcases Finset.mem_insert.1 hu with e | hu
      · rw [e]
        exact Finset.mem_inter.2 ⟨hz'.1, self_mem_inN z⟩
      · exact Finset.mem_inter.2 ⟨hCN hu, hCin z hz'.1 hu⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hz'.2] at hle
    omega

end

section

variable {n : Nat} {A : Mat} {k t lam : Int}

theorem TwinMuOne_colEq (u : Fin n → ℝ) (j : Fin n) :
    ((toR n A - (-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))ᵀ *ᵥ u) j =
      (∑ i : Fin n, (A i j : ℝ) * u i) + u j := by
  have e1 : ((toR n A)ᵀ *ᵥ u) j = ∑ i : Fin n, (A i j : ℝ) * u i := by
    simp [Matrix.mulVec, dotProduct, toR]
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, Matrix.sub_mulVec,
    Pi.sub_apply, Matrix.smul_mulVec, Pi.smul_apply, Matrix.one_mulVec, smul_eq_mul, e1]
  ring

theorem TwinMuOne_colInd (h : IsDSRG n A k t lam 1) (u : Fin n → ℝ) (j : Fin n) :
    ((toR n A - (-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))ᵀ *ᵥ u) j =
      ∑ i : Fin n, (if i ∈ inN A j then (1 : ℝ) else 0) * u i := by
  rw [TwinMuOne_colEq]
  have e : ∀ i : Fin n, (if i ∈ inN A j then (1 : ℝ) else 0) * u i =
      (A i j : ℝ) * u i + (if i = j then u i else 0) := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp [self_mem_inN, h.2.1 i i.isLt]
    · rcases h.1 i i.isLt j j.isLt with e | e <;> simp [mem_inN, hij, e]
  rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib]
  simp

theorem TwinMuOne_rank_of_supp (h : IsDSRG n A k t lam 1) (R : Finset (Fin n))
    (hR : ∀ u : Fin n → ℝ, (∀ i, i ∉ R → u i = 0) →
      (∀ j, ∑ i : Fin n, (if i ∈ inN A j then (1 : ℝ) else 0) * u i = 0) → ∀ i, u i = 0) :
    R.card ≤ (toR n A - (-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).rank := by
  classical
  rw [← Matrix.rank_transpose]
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin n) ℝ,
      M = (toR n A - (-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))ᵀ := ⟨_, rfl⟩
  rw [← hM]
  let ι : (R → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun z i => if hi : i ∈ R then z ⟨i, hi⟩ else 0
      map_add' := by
        intro a b
        funext i
        by_cases hi : i ∈ R <;> simp [hi]
      map_smul' := by
        intro c a
        funext i
        by_cases hi : i ∈ R <;> simp [hi] }
  have hinj : Function.Injective (M.mulVecLin ∘ₗ ι) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz' : M *ᵥ (ι z) = 0 := by
      rw [LinearMap.comp_apply, Matrix.mulVecLin_apply] at hz
      exact hz
    have hu0 : ∀ i, i ∉ R → ι z i = 0 := by
      intro i hi
      show (if hi' : i ∈ R then z ⟨i, hi'⟩ else 0) = 0
      simp [hi]
    have hcol : ∀ j, ∑ i : Fin n, (if i ∈ inN A j then (1 : ℝ) else 0) * ι z i = 0 := by
      intro j
      rw [← TwinMuOne_colInd h (ι z) j, ← hM]
      exact congrFun hz' j
    have hall := hR (ι z) hu0 hcol
    funext ⟨i, hi⟩
    have e : ι z i = z ⟨i, hi⟩ := by
      show (if hi' : i ∈ R then z ⟨i, hi'⟩ else 0) = z ⟨i, hi⟩
      simp [hi]
    show z ⟨i, hi⟩ = 0
    rw [← e]
    exact hall i
  have h1 : Module.finrank ℝ (LinearMap.range (M.mulVecLin ∘ₗ ι)) = R.card := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe]
  have h2 : LinearMap.range (M.mulVecLin ∘ₗ ι) ≤ LinearMap.range M.mulVecLin :=
    LinearMap.range_comp_le_range _ _
  have h3 := Submodule.finrank_mono h2
  rw [h1] at h3
  exact h3

theorem TwinMuOne_rank_ge (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (x : Fin n) :
    (insert x (outN A x \ rowCl A x)).card ≤
      (toR n A - (-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).rank := by
  classical
  apply TwinMuOne_rank_of_supp h
  intro u hu0 hcol
  have hmem : ∀ i, i ∈ insert x (outN A x \ rowCl A x) ↔
      i = x ∨ i ∈ outN A x \ rowCl A x := fun i => Finset.mem_insert
  have hSout : ∀ i ∈ insert x (outN A x \ rowCl A x), i ∈ outN A x := by
    intro i hi
    rcases (hmem i).1 hi with e | e
    · rw [e]
      exact self_mem_outN x
    · exact (Finset.mem_sdiff.1 e).1
  have step1 : ∀ o ∈ outN A x \ rowCl A x, u o = 0 := by
    intro o ho
    have ho' := Finset.mem_sdiff.1 ho
    have hne : outN A o ≠ outN A x := fun e => ho'.2 (mem_rowCl.2 e)
    obtain ⟨w, hwo, hwx⟩ := TwinMuOne_exists_out h hne
    have h1 := TwinMuOne_inter_out h ht hwx
    have hoin : o ∈ outN A x ∩ inN A w := Finset.mem_inter.2 ⟨ho'.1, out_iff_in.1 hwo⟩
    have e := hcol w
    rw [Finset.sum_eq_single o] at e
    · simpa [out_iff_in.1 hwo] using e
    · intro i _ hio
      by_cases hiS : i ∈ insert x (outN A x \ rowCl A x)
      · by_cases hiw : i ∈ inN A w
        · have hi2 : i ∈ outN A x ∩ inN A w := Finset.mem_inter.2 ⟨hSout i hiS, hiw⟩
          exact absurd (Finset.card_le_one.1 (le_of_eq h1) i hi2 o hoin) hio
        · simp [hiw]
      · simp [hu0 i hiS]
    · simp
  have step2 : u x = 0 := by
    have e := hcol x
    rw [Finset.sum_eq_single x] at e
    · simpa [self_mem_inN] using e
    · intro i _ hix
      by_cases hiS : i ∈ insert x (outN A x \ rowCl A x)
      · rcases (hmem i).1 hiS with e' | e'
        · exact absurd e' hix
        · simp [step1 i e']
      · simp [hu0 i hiS]
    · simp
  intro i
  by_cases hiS : i ∈ insert x (outN A x \ rowCl A x)
  · rcases (hmem i).1 hiS with e | e
    · rw [e]
      exact step2
    · exact step1 i e
  · exact hu0 i hiS

/-- `|{x} ∪ (N⁺[x] ∖ C_x)| = k + 2 − a`. -/
theorem TwinMuOne_card_S (h : IsDSRG n A k t lam 1) (x : Fin n) :
    ((insert x (outN A x \ rowCl A x)).card : Int) = k + 2 - (rowCl A x).card := by
  have hx : x ∉ outN A x \ rowCl A x := fun hx => (Finset.mem_sdiff.1 hx).2 (self_mem_rowCl x)
  rw [Finset.card_insert_of_notMem hx]
  have e1 := Finset.card_sdiff_add_card_eq_card (rowCl_sub_out (A := A) x)
  have e := TwinMuOne_card_out h x
  push_cast
  omega

theorem TwinMuOne_spec (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (hl : 0 ≤ lam) (hn : 0 < n) :
    (toR n A - (-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).rank =
        1 + Module.finrank ℝ (eigA n A (lam : ℝ)) ∧
      (lam + 1) * (Module.finrank ℝ (eigA n A (lam : ℝ)) : Int) = n - 1 - k := by
  have hd : disc t lam 1 = (lam + 1) ^ 2 := by
    unfold disc
    rw [ht]
    ring
  have hpos : 0 < disc t lam 1 := by
    rw [hd]
    positivity
  have hc : Real.sqrt (disc t lam 1 : ℝ) = (lam : ℝ) + 1 := by
    rw [hd]
    push_cast
    exact Real.sqrt_sq (by positivity)
  have hrR : rR t lam 1 = lam := by
    unfold rR
    rw [hc]
    push_cast
    ring
  have hsR : sR t lam 1 = -1 := by
    unfold sR
    rw [hc]
    push_cast
    ring
  have hr : IsRootPair t lam 1 (-1) (lam : ℝ) := by
    refine ⟨?_, ?_⟩
    · push_cast
      ring
    · rw [ht]
      push_cast
      ring
  refine ⟨rank_sub_root h hn hpos one_ne_zero hr, ?_⟩
  obtain ⟨_, _, hsum, htr⟩ := spectrum_counts h hn hpos one_ne_zero
  rw [hrR, hsR] at hsum htr
  set f := Module.finrank ℝ (eigA n A (lam : ℝ)) with hf
  set g := Module.finrank ℝ (eigA n A (-1)) with hg
  have hfg : (f : ℝ) + g = (n : ℝ) - 1 := by
    have : ((f + g : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) := by rw [hsum]
    push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne')] at this
    linarith
  have hR : ((lam : ℝ) + 1) * f = n - 1 - k := by linarith
  exact_mod_cast hR

theorem TwinMuOne_rank (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (hl : 0 ≤ lam) (x : Fin n) :
    k + 1 - (Module.finrank ℝ (eigA n A (lam : ℝ)) : Int) ≤ (rowCl A x).card := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) x.isLt
  have h1 := TwinMuOne_rank_ge h ht x
  rw [(TwinMuOne_spec h ht hl hn).1] at h1
  have h2 := TwinMuOne_card_S h x
  have h3 : ((insert x (outN A x \ rowCl A x)).card : Int) ≤
      1 + (Module.finrank ℝ (eigA n A (lam : ℝ)) : Int) := by exact_mod_cast h1
  omega

theorem TwinMuOne_admissible (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (hl : 0 ≤ lam) (htk : t < k)
    (x : Fin n) :
    (lam + 1) * (k + 1 - (rowCl A x).card) ≤ n - 1 - k ∧
      ((rowCl A x).card : Int) * (lam + 2 - (rowCl A x).card) ≤ k + 1 - (rowCl A x).card ∧
      ((rowCl A x).card : Int) ≤ lam + 1 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) x.isLt
  have hr := TwinMuOne_rank h ht hl x
  have hf := (TwinMuOne_spec h ht hl hn).2
  obtain ⟨hc1, hc2⟩ := TwinMuOne_class h ht htk x
  refine ⟨?_, hc1, hc2⟩
  have hl1 : 0 ≤ lam + 1 := by omega
  nlinarith [mul_le_mul_of_nonneg_left hr hl1]

theorem TwinMuOne_no_40_9_6_5_1 (A : Mat) : ¬ IsDSRG 40 A 9 6 5 1 := by
  intro h
  have x : Fin 40 := ⟨0, by norm_num⟩
  obtain ⟨h1, h2, h3⟩ := TwinMuOne_admissible h (by norm_num) (by norm_num) (by norm_num) x
  generalize ((rowCl A x).card : Int) = a at h1 h2 h3
  push_cast at h1
  have ha5 : 5 ≤ a := by linarith
  have ha6 : a ≤ 6 := by linarith
  interval_cases a <;> omega

theorem TwinMuOne_no_96_15_10_9_1 (A : Mat) : ¬ IsDSRG 96 A 15 10 9 1 := by
  intro h
  have x : Fin 96 := ⟨0, by norm_num⟩
  obtain ⟨h1, h2, h3⟩ := TwinMuOne_admissible h (by norm_num) (by norm_num) (by norm_num) x
  generalize ((rowCl A x).card : Int) = a at h1 h2 h3
  push_cast at h1
  have ha8 : 8 ≤ a := by linarith
  have ha10 : a ≤ 10 := by linarith
  interval_cases a <;> omega

end

section

variable {n : Nat} {A : Mat} {k t lam : Int}

theorem TwinMuOne_two_or (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (hk : k = 2 * lam + 2)
    (hl : 4 ≤ lam) (x : Fin n) (h2 : 2 ≤ (rowCl A x).card) :
    (rowCl A x).card = 2 ∨ ((rowCl A x).card : Int) = lam + 1 := by
  have htk : t < k := by omega
  obtain ⟨hc1, hc2⟩ := TwinMuOne_class h ht htk x
  have ha2 : (2 : Int) ≤ (rowCl A x).card := by exact_mod_cast h2
  suffices hs : ((rowCl A x).card : Int) = 2 ∨ ((rowCl A x).card : Int) = lam + 1 by
    rcases hs with e | e
    · left
      exact_mod_cast e
    · exact Or.inr e
  generalize ((rowCl A x).card : Int) = a at hc1 hc2 ha2 ⊢
  by_cases e2 : a = 2
  · exact Or.inl e2
  · by_cases e3 : a = lam + 1
    · exact Or.inr e3
    · exfalso
      have p1 : 1 ≤ a - 2 := by omega
      have p2 : 1 ≤ lam + 1 - a := by omega
      nlinarith [mul_nonneg (sub_nonneg.2 p1) (sub_nonneg.2 p2)]

theorem TwinMuOne_no_big (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (hk : k = 2 * lam + 2)
    (hl : 4 ≤ lam) (hcol : ∀ z : Fin n, 2 ≤ (colCl A z).card) (x : Fin n) :
    ((rowCl A x).card : Int) ≠ lam + 1 := by
  classical
  intro ha
  have htk : t < k := by omega
  have hd2 : ∀ y ∈ rowCl A x, (colCl A y).card = 2 := by
    intro y hy
    have had := TwinMuOne_ad h ht htk y
    rw [rowCl_eq hy] at had
    have := hcol y
    omega
  have hdisj : ((rowCl A x : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint (colCl A) := by
    intro y1 hy1 y2 hy2 hne
    show Disjoint (colCl A y1) (colCl A y2)
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    have e1 := mem_colCl.1 hz1
    have e2 := mem_colCl.1 hz2
    have hc : y2 ∈ colCl A y1 := mem_colCl.2 (e2.symm.trans e1)
    have hr : y2 ∈ rowCl A y1 := by
      rw [rowCl_eq (Finset.mem_coe.1 hy1)]
      exact Finset.mem_coe.1 hy2
    exact hne (TwinMuOne_double h ht htk hr hc).symm
  have hUcard : ((rowCl A x).biUnion (colCl A)).card = (rowCl A x).card * 2 := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hd2, Finset.sum_const, smul_eq_mul]
  have hUN : (rowCl A x).biUnion (colCl A) ⊆ outN A x := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := Finset.mem_biUnion.1 hz
    exact TwinMuOne_col_union (twin_out hy) hzy
  have e1 := Finset.card_sdiff_add_card_eq_card hUN
  have e2 := TwinMuOne_card_out h x
  have hpos : 0 < (outN A x \ (rowCl A x).biUnion (colCl A)).card := by omega
  obtain ⟨u, hu⟩ := Finset.card_pos.1 hpos
  have hu' := Finset.mem_sdiff.1 hu
  have hDu : colCl A u ⊆ outN A x \ (rowCl A x).biUnion (colCl A) := by
    intro z hz
    refine Finset.mem_sdiff.2 ⟨TwinMuOne_col_union hu'.1 hz, ?_⟩
    intro hzU
    obtain ⟨y, hy, hzy⟩ := Finset.mem_biUnion.1 hzU
    apply hu'.2
    refine Finset.mem_biUnion.2 ⟨y, hy, ?_⟩
    rw [mem_colCl, ← mem_colCl.1 hz]
    exact mem_colCl.1 hzy
  have hle := Finset.card_le_card hDu
  have := hcol u
  omega

theorem rowCl_transpose (x : Fin n) : rowCl (transpose A) x = colCl A x := rfl

theorem colCl_transpose (x : Fin n) : colCl (transpose A) x = rowCl A x := rfl

theorem TwinMuOne_family (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (hk : k = 2 * lam + 2)
    (hl : 4 ≤ lam) (hrow : ∀ z : Fin n, 2 ≤ (rowCl A z).card)
    (hcol : ∀ z : Fin n, 2 ≤ (colCl A z).card) (x : Fin n) : False := by
  classical
  have hT := isDSRG_transpose h
  have hc2 : ∀ z : Fin n, (colCl A z).card = 2 := by
    intro z
    have hrowT : ∀ w : Fin n, 2 ≤ (rowCl (transpose A) w).card := hcol
    have hcolT : ∀ w : Fin n, 2 ≤ (colCl (transpose A) w).card := hrow
    rcases TwinMuOne_two_or hT ht hk hl z (hrowT z) with e | e
    · exact e
    · exact absurd e (TwinMuOne_no_big hT ht hk hl hcolT z)
  have hNK : outN A x = ((outN A x).image (colCl A)).biUnion id := by
    ext z
    simp only [Finset.mem_biUnion, id_eq, Finset.mem_image]
    constructor
    · intro hz
      exact ⟨colCl A z, ⟨z, hz, rfl⟩, self_mem_colCl z⟩
    · rintro ⟨D, ⟨y, hy, rfl⟩, hzD⟩
      exact TwinMuOne_col_union hy hzD
  have hdisj : (((outN A x).image (colCl A) : Finset (Finset (Fin n))) :
      Set (Finset (Fin n))).PairwiseDisjoint id := by
    intro D1 hD1 D2 hD2 hne
    obtain ⟨y1, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hD1)
    obtain ⟨y2, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hD2)
    show Disjoint (colCl A y1) (colCl A y2)
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    apply hne
    show colCl A y1 = colCl A y2
    rw [← colCl_eq hz1, colCl_eq hz2]
  have hsum : ∀ D ∈ (outN A x).image (colCl A), (id D).card = 2 := by
    intro D hD
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hD
    exact hc2 y
  have e3 := Finset.card_biUnion hdisj
  rw [← hNK, Finset.sum_congr rfl hsum, Finset.sum_const, smul_eq_mul] at e3
  have e := TwinMuOne_card_out h x
  omega

theorem TwinMuOne_no_66_10_5_4_1_of_twins (A : Mat) (h : IsDSRG 66 A 10 5 4 1)
    (hrow : ∀ z : Fin 66, 2 ≤ (rowCl A z).card) (hcol : ∀ z : Fin 66, 2 ≤ (colCl A z).card) :
    False :=
  TwinMuOne_family h (by norm_num) (by norm_num) (by norm_num) hrow hcol (⟨0, by norm_num⟩ : Fin _)

theorem TwinMuOne_no_91_12_6_5_1_of_twins (A : Mat) (h : IsDSRG 91 A 12 6 5 1)
    (hrow : ∀ z : Fin 91, 2 ≤ (rowCl A z).card) (hcol : ∀ z : Fin 91, 2 ≤ (colCl A z).card) :
    False :=
  TwinMuOne_family h (by norm_num) (by norm_num) (by norm_num) hrow hcol (⟨0, by norm_num⟩ : Fin _)

end

section

variable {n : Nat} {A : Mat} {k t lam : Int}

theorem TwinMuOne_order (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (hn : 0 < n) :
    (n : Int) = (k + 1) * (k - lam) := by
  have e := k_sq h hn
  rw [ht] at e
  push_cast at e
  have e' : ((n : Int) : ℝ) = (((k + 1) * (k - lam) : Int) : ℝ) := by
    push_cast
    linear_combination (-1 : ℝ) * e
  exact_mod_cast e'

theorem TwinMuOne_rank_free (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (hk : k = 2 * lam + 2)
    (hl : 0 ≤ lam) (hn : 0 < n) :
    ((toR n A - (-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).rank : Int) = k + 2 := by
  obtain ⟨h1, h2⟩ := TwinMuOne_spec h ht hl hn
  have ho := TwinMuOne_order h ht hn
  rw [h1]
  push_cast
  have e : (lam + 1) * (Module.finrank ℝ (eigA n A (lam : ℝ)) : Int) = (lam + 1) * (k + 1) := by
    rw [h2, ho, hk]
    ring
  have hpos : lam + 1 ≠ 0 := by omega
  have := mul_left_cancel₀ hpos e
  omega

def ind (A : Mat) (w j : Fin n) : Int := if j ∈ outN A w then 1 else 0

theorem ind_eq_one {w j : Fin n} : ind A w j = 1 ↔ j ∈ outN A w := by
  unfold ind
  split_ifs with hj <;> simp [hj]

theorem ind_eq_zero {w j : Fin n} : ind A w j = 0 ↔ j ∉ outN A w := by
  unfold ind
  split_ifs with hj <;> simp [hj]

theorem ind_bound (w j : Fin n) : 0 ≤ ind A w j ∧ ind A w j ≤ 1 := by
  unfold ind
  split_ifs <;> norm_num

theorem ind_self (w : Fin n) : ind A w w = 1 := ind_eq_one.2 (self_mem_outN w)

theorem ind_in {w p : Fin n} : (if w ∈ inN A p then (1 : ℝ) else 0) = (ind A w p : ℝ) := by
  unfold ind
  by_cases hp : p ∈ outN A w
  · simp [hp, out_iff_in.1 hp]
  · have : w ∉ inN A p := fun hm => hp (out_iff_in.2 hm)
    simp [hp, this]

def blk (A : Mat) (x o : Fin n) : Finset (Fin n) := outN A o \ outN A x

theorem mem_blk {x o w : Fin n} : w ∈ blk A x o ↔ w ∈ outN A o ∧ w ∉ outN A x := by
  simp [blk]

theorem TwinMuOne_root_unique (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) {x w o o' : Fin n}
    (hw : w ∉ outN A x) (ho : o ∈ outN A x) (ho' : o' ∈ outN A x)
    (hwo : w ∈ outN A o) (hwo' : w ∈ outN A o') : o = o' := by
  have h1 := TwinMuOne_inter_out h ht hw
  exact Finset.card_le_one.1 (le_of_eq h1) o (Finset.mem_inter.2 ⟨ho, out_iff_in.1 hwo⟩)
    o' (Finset.mem_inter.2 ⟨ho', out_iff_in.1 hwo'⟩)

theorem TwinMuOne_root_exists (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) {x w : Fin n}
    (hw : w ∉ outN A x) : ∃ o ∈ outN A x, w ∈ outN A o := by
  have h1 := TwinMuOne_inter_out h ht hw
  obtain ⟨o, ho⟩ := Finset.card_pos.1 (by omega : 0 < (outN A x ∩ inN A w).card)
  have ho' := Finset.mem_inter.1 ho
  exact ⟨o, ho'.1, out_iff_in.2 ho'.2⟩

theorem TwinMuOne_blk_in (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) {x o w : Fin n}
    (ho : o ∈ outN A x) (hw : w ∈ blk A x o) :
    ((blk A x o ∩ inN A w).card : Int) = lam + 1 := by
  have hw' := mem_blk.1 hw
  have e := TwinMuOne_inter_in h ht hw'.1
  have hsplit : outN A o ∩ inN A w = insert o (blk A x o ∩ inN A w) := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_insert, mem_blk]
    constructor
    · rintro ⟨hj1, hj2⟩
      by_cases hjx : j ∈ outN A x
      · left
        exact TwinMuOne_root_unique h ht hw'.2 hjx ho (out_iff_in.2 hj2) hw'.1
      · right
        exact ⟨⟨hj1, hjx⟩, hj2⟩
    · rintro (e | ⟨⟨hj1, _⟩, hj2⟩)
      · rw [e]
        exact ⟨self_mem_outN _, out_iff_in.1 hw'.1⟩
      · exact ⟨hj1, hj2⟩
  have hno : o ∉ blk A x o ∩ inN A w := by
    intro hm
    exact (mem_blk.1 (Finset.mem_inter.1 hm).1).2 ho
  rw [hsplit, Finset.card_insert_of_notMem hno] at e
  push_cast at e
  omega

theorem TwinMuOne_blk_in_other (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) {x o o' w : Fin n}
    (ho : o ∈ outN A x) (ho' : o' ∈ outN A x) (hne : o ≠ o') (hw : w ∈ blk A x o') :
    (blk A x o ∩ inN A w).card ≤ 1 := by
  have hw' := mem_blk.1 hw
  have hwo : w ∉ outN A o := fun hwo => hne (TwinMuOne_root_unique h ht hw'.2 ho ho' hwo hw'.1)
  have e := TwinMuOne_inter_out h ht hwo
  have hsub : blk A x o ∩ inN A w ⊆ outN A o ∩ inN A w := by
    intro j hj
    have hj' := Finset.mem_inter.1 hj
    exact Finset.mem_inter.2 ⟨(mem_blk.1 hj'.1).1, hj'.2⟩
  have := Finset.card_le_card hsub
  omega

theorem TwinMuOne_blk_nonempty (h : IsDSRG n A k t lam 1) {x o : Fin n}
    (hfree : ∀ y, outN A y = outN A x → y = x) (hox : o ≠ x) : (blk A x o).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro he
  have hsub : outN A o ⊆ outN A x := by
    intro j hj
    by_contra hjx
    have : j ∈ blk A x o := mem_blk.2 ⟨hj, hjx⟩
    rw [he] at this
    simp at this
  exact hox (hfree o (TwinMuOne_out_eq h hsub))

theorem TwinMuOne_blk_sum (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (x : Fin n) :
    ∑ o ∈ (outN A x).erase x, ((blk A x o).card : Int) = n - (k + 1) := by
  classical
  have hU : ((outN A x).erase x).biUnion (blk A x) = Finset.univ \ outN A x := by
    ext w
    simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and,
      mem_blk]
    constructor
    · rintro ⟨o, _, _, hw⟩
      exact hw
    · intro hw
      obtain ⟨o, ho, hwo⟩ := TwinMuOne_root_exists h ht hw
      refine ⟨o, ⟨?_, ho⟩, hwo, hw⟩
      intro e
      rw [e] at hwo
      exact hw hwo
  have hdisj : (((outN A x).erase x : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
      (blk A x) := by
    intro o1 ho1 o2 ho2 hne
    show Disjoint (blk A x o1) (blk A x o2)
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    have a1 := mem_blk.1 hw1
    have a2 := mem_blk.1 hw2
    exact hne (TwinMuOne_root_unique h ht a1.2 (Finset.mem_of_mem_erase (Finset.mem_coe.1 ho1))
      (Finset.mem_of_mem_erase (Finset.mem_coe.1 ho2)) a1.1 a2.1)
  have e1 := Finset.card_biUnion hdisj
  have e2 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (outN A x))
  rw [Finset.card_univ, Fintype.card_fin] at e2
  have e3 := TwinMuOne_card_out h x
  have e4 : ((∑ o ∈ (outN A x).erase x, (blk A x o).card : Nat) : Int) = n - (k + 1) := by
    rw [← e1, hU]
    omega
  exact_mod_cast e4

theorem TwinMuOne_col_blk (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) {x o w w' p : Fin n}
    (u : Fin n → ℝ) (ho : o ∈ outN A x) (hp : p ∈ blk A x o) (hw : w ∉ outN A x)
    (hw' : w' ∉ outN A x) (hww : w ≠ w')
    (hu : ∀ i, i ∉ insert w (insert w' (outN A x)) → u i = 0) :
    ∑ i : Fin n, (if i ∈ inN A p then (1 : ℝ) else 0) * u i =
      u o + (ind A w p : ℝ) * u w + (ind A w' p : ℝ) * u w' := by
  have hp' := mem_blk.1 hp
  have hpt : ∀ i : Fin n, (if i ∈ inN A p then (1 : ℝ) else 0) * u i =
      (if i = o then u i else 0) + (if i = w then (ind A w p : ℝ) * u i else 0) +
        (if i = w' then (ind A w' p : ℝ) * u i else 0) := by
    intro i
    rw [ind_in]
    by_cases hio : i = o
    · rw [hio]
      have h1 : o ≠ w := fun e => hw (e ▸ ho)
      have h2 : o ≠ w' := fun e => hw' (e ▸ ho)
      have h3 : ind A o p = 1 := ind_eq_one.2 hp'.1
      simp [h1, h2, h3]
    · by_cases hiw : i = w
      · rw [hiw]
        have h1 : w ≠ o := fun e => hio (hiw.trans e)
        simp [h1, hww]
      · by_cases hiw' : i = w'
        · rw [hiw']
          have h1 : w' ≠ o := fun e => hio (hiw'.trans e)
          have h2 : w' ≠ w := fun e => hiw (hiw'.trans e)
          simp [h1, h2]
        · simp only [hio, hiw, hiw', ite_false, add_zero]
          by_cases hix : i ∈ outN A x
          · have : ind A i p = 0 := ind_eq_zero.2 (fun hm =>
              hio (TwinMuOne_root_unique h ht hp'.2 hix ho hm hp'.1))
            simp [this]
          · have : u i = 0 := hu i (by simp [hiw, hiw', hix])
            simp [this]
  rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp

theorem TwinMuOne_det (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (hk : k = 2 * lam + 2)
    (hl : 0 ≤ lam) {x : Fin n} (hfree : ∀ y, outN A y = outN A x → y = x)
    {o o' w w' p q p' q' : Fin n} (ho : o ∈ outN A x) (ho' : o' ∈ outN A x)
    (hw : w ∉ outN A x) (hw' : w' ∉ outN A x)
    (hp : p ∈ blk A x o) (hq : q ∈ blk A x o) (hp' : p' ∈ blk A x o')
    (hq' : q' ∈ blk A x o') :
    (ind A w p - ind A w q) * (ind A w' p' - ind A w' q') =
      (ind A w' p - ind A w' q) * (ind A w p' - ind A w q') := by
  classical
  by_cases hww : w = w'
  · rw [hww]
  by_contra hD
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) x.isLt
  have hcard : ((insert w (insert w' (outN A x))).card : Int) = k + 3 := by
    have h1 : w ∉ insert w' (outN A x) := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨hww, hw⟩
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem hw']
    push_cast
    rw [TwinMuOne_card_out h x]
    ring
  have hrank := TwinMuOne_rank_free h ht hk hl hn
  have hle := TwinMuOne_rank_of_supp h (insert w (insert w' (outN A x))) ?_
  · have : ((insert w (insert w' (outN A x))).card : Int) ≤ k + 2 := by
      rw [← hrank]
      exact_mod_cast hle
    omega
  intro u hu hcol
  have cp := hcol p
  have cq := hcol q
  have cp' := hcol p'
  have cq' := hcol q'
  rw [TwinMuOne_col_blk h ht u ho hp hw hw' hww hu] at cp
  rw [TwinMuOne_col_blk h ht u ho hq hw hw' hww hu] at cq
  rw [TwinMuOne_col_blk h ht u ho' hp' hw hw' hww hu] at cp'
  rw [TwinMuOne_col_blk h ht u ho' hq' hw hw' hww hu] at cq'
  have hD' : ((ind A w p : ℝ) - ind A w q) * ((ind A w' p' : ℝ) - ind A w' q') -
      ((ind A w' p : ℝ) - ind A w' q) * ((ind A w p' : ℝ) - ind A w q') ≠ 0 := by
    intro e
    apply hD
    have e' : (((ind A w p - ind A w q) * (ind A w' p' - ind A w' q') -
        (ind A w' p - ind A w' q) * (ind A w p' - ind A w q') : Int) : ℝ) = 0 := by
      push_cast
      exact e
    have e'' := (Int.cast_eq_zero (α := ℝ)).1 e'
    linarith
  have e1 : ((ind A w p : ℝ) - ind A w q) * u w +
      ((ind A w' p : ℝ) - ind A w' q) * u w' = 0 := by linarith
  have e2 : ((ind A w p' : ℝ) - ind A w q') * u w +
      ((ind A w' p' : ℝ) - ind A w' q') * u w' = 0 := by linarith
  have huw : u w = 0 := by
    have e3 : u w * (((ind A w p : ℝ) - ind A w q) * ((ind A w' p' : ℝ) - ind A w' q') -
        ((ind A w' p : ℝ) - ind A w' q) * ((ind A w p' : ℝ) - ind A w q')) = 0 := by
      linear_combination ((ind A w' p' : ℝ) - ind A w' q') * e1 -
        ((ind A w' p : ℝ) - ind A w' q) * e2
    rcases mul_eq_zero.1 e3 with e | e
    · exact e
    · exact absurd e hD'
  have huw' : u w' = 0 := by
    have e3 : u w' * (((ind A w p : ℝ) - ind A w q) * ((ind A w' p' : ℝ) - ind A w' q') -
        ((ind A w' p : ℝ) - ind A w' q) * ((ind A w p' : ℝ) - ind A w q')) = 0 := by
      linear_combination ((ind A w p : ℝ) - ind A w q) * e2 -
        ((ind A w p' : ℝ) - ind A w q') * e1
    rcases mul_eq_zero.1 e3 with e | e
    · exact e
    · exact absurd e hD'
  have huo : ∀ i, i ∈ outN A x → i ≠ x → u i = 0 := by
    intro i hi hix
    obtain ⟨r, hr⟩ := TwinMuOne_blk_nonempty h hfree hix
    have cr := hcol r
    rw [TwinMuOne_col_blk h ht u hi hr hw hw' hww hu, huw, huw'] at cr
    linarith
  have hz : ∀ i, i ≠ x → u i = 0 := by
    intro i hix
    by_cases hiw : i = w
    · rw [hiw]
      exact huw
    · by_cases hiw' : i = w'
      · rw [hiw']
        exact huw'
      · by_cases hi : i ∈ outN A x
        · exact huo i hi hix
        · exact hu i (by simp [hiw, hiw', hi])
  have hux : u x = 0 := by
    have cx := hcol x
    rw [Finset.sum_eq_single x] at cx
    · simpa [self_mem_inN] using cx
    · intro i _ hix
      simp [hz i hix]
    · simp
  intro i
  by_cases hix : i = x
  · rw [hix]
    exact hux
  · exact hz i hix

theorem in_iff_ind {w p : Fin n} : w ∈ inN A p ↔ ind A w p = 1 :=
  ⟨fun hm => ind_eq_one.2 (out_iff_in.2 hm), fun e => out_iff_in.1 (ind_eq_one.1 e)⟩

theorem mem_pos {x o p q w : Fin n}
    (hw : w ∈ (blk A x o ∩ inN A p) \ (blk A x o ∩ inN A q)) :
    w ∈ blk A x o ∧ ind A w p = 1 ∧ ind A w q = 0 := by
  simp only [Finset.mem_sdiff, Finset.mem_inter, not_and] at hw
  obtain ⟨⟨hb, hpi⟩, hqi⟩ := hw
  exact ⟨hb, in_iff_ind.1 hpi, ind_eq_zero.2 (fun hm => hqi hb (out_iff_in.1 hm))⟩

structure FreeV (n : Nat) (A : Mat) (k t lam : Int) (x : Fin n) : Prop where
  dsrg : IsDSRG n A k t lam 1
  ht : t = lam + 1
  hk : k = 2 * lam + 2
  hl : 1 ≤ lam
  free : ∀ y, outN A y = outN A x → y = x

structure RefV {n : Nat} (A : Mat) (x w₀ o₁ p₀ q₀ : Fin n) : Prop where
  hw : w₀ ∉ outN A x
  ho : o₁ ∈ outN A x
  hp : p₀ ∈ blk A x o₁
  hq : q₀ ∈ blk A x o₁
  ip : ind A w₀ p₀ = 1
  iq : ind A w₀ q₀ = 0

def specTw (A : Mat) (x w₀ o : Fin n) : Prop :=
  ∃ p ∈ blk A x o, ∃ q ∈ blk A x o, ind A w₀ p = 1 ∧ ind A w₀ q = 0

theorem FreeV.r1 {x w₀ o₁ p₀ q₀ : Fin n} (F : FreeV n A k t lam x)
    (R : RefV A x w₀ o₁ p₀ q₀) {o w p q : Fin n} (ho : o ∈ outN A x) (hw : w ∉ outN A x)
    (hp : p ∈ blk A x o) (hq : q ∈ blk A x o) :
    ind A w p - ind A w q = (ind A w p₀ - ind A w q₀) * (ind A w₀ p - ind A w₀ q) := by
  have e := TwinMuOne_det F.dsrg F.ht F.hk (by have := F.hl; omega) F.free R.ho ho R.hw hw R.hp R.hq
    hp hq
  rw [R.ip, R.iq] at e
  linear_combination e

theorem FreeV.r1_eq {x w₀ o₁ p₀ q₀ : Fin n} (F : FreeV n A k t lam x)
    (R : RefV A x w₀ o₁ p₀ q₀) {o w p q : Fin n} (ho : o ∈ outN A x) (hw : w ∉ outN A x)
    (hp : p ∈ blk A x o) (hq : q ∈ blk A x o) (hpq : ind A w₀ p = ind A w₀ q) :
    ind A w p = ind A w q := by
  have e := F.r1 R ho hw hp hq
  rw [hpq, sub_self, mul_zero] at e
  linarith

theorem FreeV.r1_pos {x w₀ o₁ p₀ q₀ : Fin n} (F : FreeV n A k t lam x)
    (R : RefV A x w₀ o₁ p₀ q₀) {o w p q : Fin n} (ho : o ∈ outN A x) (hw : w ∉ outN A x)
    (hp : p ∈ blk A x o) (hq : q ∈ blk A x o) (hp1 : ind A w₀ p = 1)
    (hq0 : ind A w₀ q = 0) :
    ind A w p - ind A w q = ind A w p₀ - ind A w q₀ := by
  have e := F.r1 R ho hw hp hq
  rw [hp1, hq0] at e
  linear_combination e

theorem FreeV.uniform {x : Fin n} (F : FreeV n A k t lam x) {o : Fin n} (ho : o ∈ outN A x)
    (hox : o ≠ x) (hu : ∀ w ∈ blk A x o, ∀ y ∈ blk A x o, ind A w y = 1) :
    ((blk A x o).card : Int) = lam + 1 := by
  obtain ⟨p, hp⟩ := TwinMuOne_blk_nonempty F.dsrg F.free hox
  have e := TwinMuOne_blk_in F.dsrg F.ht ho hp
  have hs : blk A x o ∩ inN A p = blk A x o := by
    apply Finset.inter_eq_left.2
    intro w hw
    exact in_iff_ind.2 (hu w hw p hp)
  rw [hs] at e
  exact e

theorem FreeV.ref {x : Fin n} (F : FreeV n A k t lam x) :
    ∃ w₀ o₁ p₀ q₀, RefV A x w₀ o₁ p₀ q₀ := by
  classical
  by_contra hno
  have hall : ∀ o ∈ (outN A x).erase x, ((blk A x o).card : Int) = lam + 1 := by
    intro o ho
    have ho' := Finset.mem_erase.1 ho
    apply F.uniform ho'.2 ho'.1
    intro w hw y hy
    by_contra hy1
    have hy0 : ind A w y = 0 := by
      have := ind_bound (A := A) w y
      omega
    exact hno ⟨w, o, w, y, (mem_blk.1 hw).2, ho'.2, hw, hy, ind_self w, hy0⟩
  have hs := TwinMuOne_blk_sum F.dsrg F.ht x
  rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul] at hs
  have hc : (((outN A x).erase x).card : Int) = k := by
    have h1 : 1 ≤ (outN A x).card := Finset.card_pos.2 ⟨x, self_mem_outN x⟩
    rw [Finset.card_erase_of_mem (self_mem_outN x), Nat.cast_sub h1, Nat.cast_one,
      TwinMuOne_card_out F.dsrg x]
    ring
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) x.isLt
  have ho := TwinMuOne_order F.dsrg F.ht hn
  rw [hc, ho, F.hk] at hs
  have := F.hl
  nlinarith

theorem FreeV.nonspec {x w₀ o₁ p₀ q₀ : Fin n} (F : FreeV n A k t lam x)
    (R : RefV A x w₀ o₁ p₀ q₀) {o : Fin n} (ho : o ∈ outN A x) (hs : ¬ specTw A x w₀ o) :
    ∀ w ∈ blk A x o, ∀ y ∈ blk A x o, ind A w y = 1 := by
  intro w hw y hy
  have hconst : ind A w₀ y = ind A w₀ w := by
    have b1 := ind_bound (A := A) w₀ y
    have b2 := ind_bound (A := A) w₀ w
    by_contra hne
    rcases (by omega : (ind A w₀ y = 1 ∧ ind A w₀ w = 0) ∨
        (ind A w₀ w = 1 ∧ ind A w₀ y = 0)) with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact hs ⟨y, hy, w, hw, e1, e2⟩
    · exact hs ⟨w, hw, y, hy, e1, e2⟩
  have e := F.r1_eq R ho (mem_blk.1 hw).2 hy hw hconst
  rw [e]
  exact ind_self w

theorem FreeV.cover {x w₀ o₁ p₀ q₀ : Fin n} (F : FreeV n A k t lam x)
    (R : RefV A x w₀ o₁ p₀ q₀) {o p q w : Fin n} (ho : o ∈ outN A x)
    (hp : p ∈ blk A x o) (hq : q ∈ blk A x o) (hp1 : ind A w₀ p = 1)
    (hq0 : ind A w₀ q = 0) (hw : w ∈ blk A x o) :
    ind A w p = 1 ∨ ind A w q = 1 := by
  have hwx := (mem_blk.1 hw).2
  have e := F.r1_pos R ho hwx hp hq hp1 hq0
  have b1 := ind_bound (A := A) w p
  have b2 := ind_bound (A := A) w q
  have bs := ind_self (A := A) w
  have b0 := ind_bound (A := A) w₀ w
  by_contra hc
  push Not at hc
  rcases (by omega : ind A w₀ w = 1 ∨ ind A w₀ w = 0) with e0 | e0
  · have e' := F.r1_pos R ho hwx hw hq e0 hq0
    omega
  · have e' := F.r1_pos R ho hwx hp hw hp1 e0
    omega

theorem FreeV.spec_card {x w₀ o₁ p₀ q₀ : Fin n} (F : FreeV n A k t lam x)
    (R : RefV A x w₀ o₁ p₀ q₀) {o p q : Fin n} (ho : o ∈ outN A x)
    (hp : p ∈ blk A x o) (hq : q ∈ blk A x o) (hp1 : ind A w₀ p = 1)
    (hq0 : ind A w₀ q = 0) :
    ((blk A x o).card : Int) +
      ((blk A x o ∩ inN A p) ∩ (blk A x o ∩ inN A q)).card = 2 * lam + 2 := by
  have hU : (blk A x o ∩ inN A p) ∪ (blk A x o ∩ inN A q) = blk A x o := by
    ext w
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw
    · intro hw
      rcases F.cover R ho hp hq hp1 hq0 hw with e | e
      · exact Or.inl ⟨hw, in_iff_ind.2 e⟩
      · exact Or.inr ⟨hw, in_iff_ind.2 e⟩
  have e1 := Finset.card_union_add_card_inter (blk A x o ∩ inN A p)
    (blk A x o ∩ inN A q)
  rw [hU] at e1
  have e2 := TwinMuOne_blk_in F.dsrg F.ht ho hp
  have e3 := TwinMuOne_blk_in F.dsrg F.ht ho hq
  omega

theorem FreeV.spec_excess {x w₀ o₁ p₀ q₀ : Fin n} (F : FreeV n A k t lam x)
    (R : RefV A x w₀ o₁ p₀ q₀) {o p q : Fin n} (ho : o ∈ outN A x)
    (hp : p ∈ blk A x o) (hq : q ∈ blk A x o) (hp1 : ind A w₀ p = 1)
    (hq0 : ind A w₀ q = 0) :
    ((blk A x o).card : Int) =
        lam + 1 + ((blk A x o ∩ inN A p) \ (blk A x o ∩ inN A q)).card ∧
      (((blk A x o ∩ inN A q) \ (blk A x o ∩ inN A p)).card : Int) =
        ((blk A x o ∩ inN A p) \ (blk A x o ∩ inN A q)).card := by
  have e0 := F.spec_card R ho hp hq hp1 hq0
  have e1 := Finset.card_sdiff_add_card_inter (blk A x o ∩ inN A p) (blk A x o ∩ inN A q)
  have e2 := Finset.card_sdiff_add_card_inter (blk A x o ∩ inN A q) (blk A x o ∩ inN A p)
  rw [Finset.inter_comm (blk A x o ∩ inN A q)] at e2
  have e3 := TwinMuOne_blk_in F.dsrg F.ht ho hp
  have e4 := TwinMuOne_blk_in F.dsrg F.ht ho hq
  constructor <;> omega

theorem FreeV.two_spec {x w₀ o₁ p₀ q₀ : Fin n} (F : FreeV n A k t lam x)
    (R : RefV A x w₀ o₁ p₀ q₀) {o o' p q p' q' : Fin n} (ho : o ∈ outN A x)
    (ho' : o' ∈ outN A x) (hne : o ≠ o')
    (hp : p ∈ blk A x o) (hq : q ∈ blk A x o) (hp1 : ind A w₀ p = 1)
    (hq0 : ind A w₀ q = 0) (hp' : p' ∈ blk A x o') (hq' : q' ∈ blk A x o')
    (hp1' : ind A w₀ p' = 1) (hq0' : ind A w₀ q' = 0) :
    ((blk A x o ∩ inN A p) \ (blk A x o ∩ inN A q)).card ≤ 1 := by
  have hsub : (blk A x o ∩ inN A p) \ (blk A x o ∩ inN A q) ⊆
      blk A x o ∩ inN A p' := by
    intro w hw
    obtain ⟨hb, e1, e2⟩ := mem_pos hw
    have hwx := (mem_blk.1 hb).2
    have c1 := F.r1_pos R ho hwx hp hq hp1 hq0
    have c2 := F.r1_pos R ho' hwx hp' hq' hp1' hq0'
    have b1 := ind_bound (A := A) w p'
    have b2 := ind_bound (A := A) w q'
    have : ind A w p' = 1 := by omega
    exact Finset.mem_inter.2 ⟨hb, in_iff_ind.2 this⟩
  exact (Finset.card_le_card hsub).trans (TwinMuOne_blk_in_other F.dsrg F.ht ho ho' hne hp')

theorem FreeV.struct {x : Fin n} (F : FreeV n A k t lam x) (hl3 : 3 ≤ lam) :
    ∃ o, o ∈ outN A x ∧ o ≠ x ∧ (∀ j ∈ outN A o, j ∈ outN A x → j = o) ∧
      ∀ u ∈ outN A o, u ≠ o →
        (∃ u' ∈ outN A o, u' ∈ outN A u ∧ u' ≠ u) ∧ (∃ u'' ∈ outN A o, u'' ∉ outN A u) := by
  classical
  obtain ⟨w₀, o₁, p₀, q₀, R⟩ := F.ref
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) x.isLt
  have hO : (((outN A x).erase x).card : Int) = k := by
    have h1 : 1 ≤ (outN A x).card := Finset.card_pos.2 ⟨x, self_mem_outN x⟩
    rw [Finset.card_erase_of_mem (self_mem_outN x), Nat.cast_sub h1, Nat.cast_one,
      TwinMuOne_card_out F.dsrg x]
    ring
  have hsum := TwinMuOne_blk_sum F.dsrg F.ht x
  have hord := TwinMuOne_order F.dsrg F.ht hn
  have hk := F.hk
  have hnon : ∀ o ∈ (outN A x).erase x, ¬ specTw A x w₀ o →
      ((blk A x o).card : Int) - (lam + 1) = 0 := by
    intro o ho hs
    have ho' := Finset.mem_erase.1 ho
    rw [F.uniform ho'.2 ho'.1 (F.nonspec R ho'.2 hs)]
    ring
  have htot : ∑ o ∈ (outN A x).erase x, (((blk A x o).card : Int) - (lam + 1)) = lam + 1 := by
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, nsmul_eq_mul, hO, hord, hk]
    ring
  set SP := ((outN A x).erase x).filter (fun o => specTw A x w₀ o) with hSPdef
  have hSP : ∑ o ∈ SP, (((blk A x o).card : Int) - (lam + 1)) = lam + 1 := by
    have e := Finset.sum_filter_add_sum_filter_not ((outN A x).erase x)
      (fun o => specTw A x w₀ o) (fun o => ((blk A x o).card : Int) - (lam + 1))
    have : ∑ o ∈ ((outN A x).erase x).filter (fun o => ¬ specTw A x w₀ o),
        (((blk A x o).card : Int) - (lam + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro o ho
      have ho' := Finset.mem_filter.1 ho
      exact hnon o ho'.1 ho'.2
    rw [this, add_zero, htot] at e
    exact e
  by_cases h2 : ∃ a ∈ SP, ∃ b ∈ SP, a ≠ b
  ·
    exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := h2
    have hpart : ∀ o ∈ SP, ∃ o' ∈ SP, o' ≠ o := by
      intro o ho
      by_cases hoa : o = a
      · refine ⟨b, hb, ?_⟩
        rw [hoa]
        exact fun e => hab e.symm
      · exact ⟨a, ha, fun e => hoa e.symm⟩
    have hle1 : ∀ o ∈ SP, ((blk A x o).card : Int) - (lam + 1) ≤ 1 := by
      intro o ho
      have ho' := Finset.mem_filter.1 ho
      obtain ⟨p, hp, q, hq, hp1, hq0⟩ := ho'.2
      obtain ⟨o', ho'', hne⟩ := hpart o ho
      have ho''' := Finset.mem_filter.1 ho''
      obtain ⟨p', hp', q', hq', hp1', hq0'⟩ := ho'''.2
      have hoS := (Finset.mem_erase.1 ho'.1).2
      have ho'S := (Finset.mem_erase.1 ho'''.1).2
      have e := (F.spec_excess R hoS hp hq hp1 hq0).1
      have e2 := F.two_spec R hoS ho'S (Ne.symm hne) hp hq hp1 hq0 hp' hq' hp1' hq0'
      omega
    have hcard : lam + 1 ≤ (SP.card : Int) := by
      have : ∑ o ∈ SP, (((blk A x o).card : Int) - (lam + 1)) ≤ ∑ _o ∈ SP, (1 : Int) :=
        Finset.sum_le_sum hle1
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, hSP] at this
      exact this
    obtain ⟨o, ho, hpos⟩ : ∃ o ∈ SP, 1 ≤ ((blk A x o).card : Int) - (lam + 1) := by
      by_contra hc
      push Not at hc
      have : ∑ o ∈ SP, (((blk A x o).card : Int) - (lam + 1)) ≤ ∑ _o ∈ SP, (0 : Int) :=
        Finset.sum_le_sum (fun o ho => by have := hc o ho; omega)
      rw [Finset.sum_const_zero, hSP] at this
      have := F.hl
      omega
    have ho' := Finset.mem_filter.1 ho
    obtain ⟨p, hp, q, hq, hp1, hq0⟩ := ho'.2
    have hoS := (Finset.mem_erase.1 ho'.1).2
    obtain ⟨eA, eB⟩ := F.spec_excess R hoS hp hq hp1 hq0
    obtain ⟨wm, hwm⟩ : ((blk A x o ∩ inN A q) \ (blk A x o ∩ inN A p)).Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨hwmb, hwmq, hwmp⟩ := mem_pos hwm
    have hwmx := (mem_blk.1 hwmb).2
    have cwm := F.r1_pos R hoS hwmx hp hq hp1 hq0
    have hcov : SP.biUnion (blk A x) ⊆ outN A w₀ ∪ outN A wm := by
      intro y hy
      obtain ⟨o2, ho2, hy2⟩ := Finset.mem_biUnion.1 hy
      have ho2' := Finset.mem_filter.1 ho2
      obtain ⟨p2, hp2, q2, hq2, hp21, hq20⟩ := ho2'.2
      have ho2S := (Finset.mem_erase.1 ho2'.1).2
      rcases (by have := ind_bound (A := A) w₀ y; omega :
          ind A w₀ y = 1 ∨ ind A w₀ y = 0) with e | e
      · exact Finset.mem_union.2 (Or.inl (ind_eq_one.1 e))
      · have c2 := F.r1_pos R ho2S hwmx hp2 hy2 hp21 e
        have b1 := ind_bound (A := A) wm p2
        have b2 := ind_bound (A := A) wm y
        have : ind A wm y = 1 := by omega
        exact Finset.mem_union.2 (Or.inr (ind_eq_one.1 this))
    have hdisj : (SP : Set (Fin n)).PairwiseDisjoint (blk A x) := by
      intro o1 ho1 o2 ho2 hne
      show Disjoint (blk A x o1) (blk A x o2)
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      have a1 := mem_blk.1 hw1
      have a2 := mem_blk.1 hw2
      have m1 := Finset.mem_filter.1 (Finset.mem_coe.1 ho1)
      have m2 := Finset.mem_filter.1 (Finset.mem_coe.1 ho2)
      exact hne (TwinMuOne_root_unique F.dsrg F.ht a1.2 (Finset.mem_of_mem_erase m1.1)
        (Finset.mem_of_mem_erase m2.1) a1.1 a2.1)
    have hU := Finset.card_biUnion hdisj
    have hle := Finset.card_le_card hcov
    have hun := Finset.card_union_le (outN A w₀) (outN A wm)
    have c0 := TwinMuOne_card_out F.dsrg w₀
    have c1 := TwinMuOne_card_out F.dsrg wm
    have hsumSP : (((SP.biUnion (blk A x)).card : Nat) : Int) =
        (SP.card : Int) * (lam + 1) + (lam + 1) := by
      rw [hU]
      push_cast
      have : ∑ o ∈ SP, ((blk A x o).card : Int) =
          ∑ o ∈ SP, ((((blk A x o).card : Int) - (lam + 1)) + (lam + 1)) := by
        apply Finset.sum_congr rfl
        intro o _
        ring
      rw [this, Finset.sum_add_distrib, hSP, Finset.sum_const, nsmul_eq_mul]
      ring
    have hfin : (SP.card : Int) * (lam + 1) + (lam + 1) ≤ 2 * k + 2 := by
      rw [← hsumSP]
      omega
    have hl1 : 0 ≤ lam + 1 := by omega
    nlinarith [mul_le_mul_of_nonneg_right hcard hl1]
  ·
    push Not at h2
    obtain ⟨o, ho⟩ : SP.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      rw [he, Finset.sum_empty] at hSP
      have := F.hl
      omega
    have hsingle : SP = {o} := by
      ext y
      simp only [Finset.mem_singleton]
      constructor
      · intro hy
        exact h2 y hy o ho
      · intro e
        rw [e]
        exact ho
    rw [hsingle, Finset.sum_singleton] at hSP
    have ho' := Finset.mem_filter.1 ho
    obtain ⟨p, hp, q, hq, hp1, hq0⟩ := ho'.2
    have hoE := Finset.mem_erase.1 ho'.1
    have hoS := hoE.2
    have hcardo : ((blk A x o).card : Int) = 2 * lam + 2 := by omega
    have hPN := F.spec_card R hoS hp hq hp1 hq0
    have hPN0 : ((blk A x o ∩ inN A p) ∩ (blk A x o ∩ inN A q)).card = 0 := by omega
    have hPc := TwinMuOne_blk_in F.dsrg F.ht hoS hp
    have hNc := TwinMuOne_blk_in F.dsrg F.ht hoS hq
    have hNo : outN A o = insert o (blk A x o) := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro j hj
        rcases Finset.mem_insert.1 hj with e | e
        · rw [e]
          exact self_mem_outN o
        · exact (mem_blk.1 e).1
      · have hno : o ∉ blk A x o := fun hm => (mem_blk.1 hm).2 hoS
        rw [Finset.card_insert_of_notMem hno]
        have := TwinMuOne_card_out F.dsrg o
        omega
    refine ⟨o, hoS, hoE.1, ?_, ?_⟩
    · intro j hj hjx
      rw [hNo] at hj
      rcases Finset.mem_insert.1 hj with e | e
      · exact e
      · exact absurd hjx (mem_blk.1 e).2
    · intro u hu huo
      rw [hNo] at hu
      have hub : u ∈ blk A x o := by
        rcases Finset.mem_insert.1 hu with e | e
        · exact absurd e huo
        · exact e
      have hux := (mem_blk.1 hub).2
      have hPN' : ∀ w ∈ blk A x o, ¬ (ind A w p = 1 ∧ ind A w q = 1) := by
        rintro w hw ⟨e1, e2⟩
        have hm : w ∈ (blk A x o ∩ inN A p) ∩ (blk A x o ∩ inN A q) :=
          Finset.mem_inter.2 ⟨Finset.mem_inter.2 ⟨hw, in_iff_ind.2 e1⟩,
            Finset.mem_inter.2 ⟨hw, in_iff_ind.2 e2⟩⟩
        rw [Finset.card_eq_zero.1 hPN0] at hm
        simp at hm
      have cu := F.r1_pos R hoS hux hp hq hp1 hq0
      have bup := ind_bound (A := A) u p
      have buq := ind_bound (A := A) u q
      have hbo : blk A x o ⊆ outN A o := fun j hj => (mem_blk.1 hj).1
      rcases F.cover R hoS hp hq hp1 hq0 hub with eu | eu
      · have euq : ind A u q = 0 := by
          have := hPN' u hub
          omega
        have h2c : 1 < (blk A x o ∩ inN A p).card := by omega
        obtain ⟨u', hu', hne⟩ := Finset.exists_mem_ne h2c u
        have hu'b := (Finset.mem_inter.1 hu').1
        have eu'p := in_iff_ind.1 (Finset.mem_inter.1 hu').2
        have eu'q : ind A u' q = 0 := by
          have := hPN' u' hu'b
          have := ind_bound (A := A) u' q
          omega
        have hu'x := (mem_blk.1 hu'b).2
        have cu' := F.r1_pos R hoS hu'x hp hq hp1 hq0
        have hw0 : ind A w₀ u' = 1 := by
          by_contra hc
          have e0 : ind A w₀ u' = 0 := by
            have := ind_bound (A := A) w₀ u'
            omega
          have := F.r1_pos R hoS hu'x hp hu'b hp1 e0
          have := ind_self (A := A) u'
          omega
        have c3 := F.r1_pos R hoS hux hu'b hq hw0 hq0
        have huu' : ind A u u' = 1 := by
          have := ind_bound (A := A) u u'
          omega
        exact ⟨⟨u', hbo hu'b, ind_eq_one.1 huu', hne⟩, ⟨q, hbo hq, ind_eq_zero.1 euq⟩⟩
      · have eup : ind A u p = 0 := by
          have := hPN' u hub
          omega
        have h2c : 1 < (blk A x o ∩ inN A q).card := by omega
        obtain ⟨u', hu', hne⟩ := Finset.exists_mem_ne h2c u
        have hu'b := (Finset.mem_inter.1 hu').1
        have eu'q := in_iff_ind.1 (Finset.mem_inter.1 hu').2
        have eu'p : ind A u' p = 0 := by
          have := hPN' u' hu'b
          have := ind_bound (A := A) u' p
          omega
        have hu'x := (mem_blk.1 hu'b).2
        have cu' := F.r1_pos R hoS hu'x hp hq hp1 hq0
        have hw0 : ind A w₀ u' = 0 := by
          by_contra hc
          have e1 : ind A w₀ u' = 1 := by
            have := ind_bound (A := A) w₀ u'
            omega
          have := F.r1_pos R hoS hu'x hu'b hq e1 hq0
          have := ind_self (A := A) u'
          omega
        have c3 := F.r1_pos R hoS hux hp hu'b hp1 hw0
        have huu' : ind A u u' = 1 := by
          have := ind_bound (A := A) u u'
          omega
        exact ⟨⟨u', hbo hu'b, ind_eq_one.1 huu', hne⟩, ⟨p, hbo hp, ind_eq_zero.1 eup⟩⟩

theorem TwinMuOne_free_twin (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (hk : k = 2 * lam + 2)
    (hl : 3 ≤ lam) (x : Fin n) : 2 ≤ (rowCl A x).card := by
  by_contra hlt
  have hfree : ∀ y, outN A y = outN A x → y = x := by
    intro y hy
    have h1 : (rowCl A x).card ≤ 1 := by omega
    exact Finset.card_le_one.1 h1 y (mem_rowCl.2 hy) x (self_mem_rowCl x)
  obtain ⟨o, -, -, -, hc⟩ := FreeV.struct ⟨h, ht, hk, by omega, hfree⟩ hl
  have hofree : ∀ y, outN A y = outN A o → y = o := by
    intro y hy
    by_contra hyo
    have hyN : y ∈ outN A o := by
      rw [← hy]
      exact self_mem_outN y
    obtain ⟨-, u'', hu''o, hu''y⟩ := hc y hyN hyo
    rw [hy] at hu''y
    exact hu''y hu''o
  obtain ⟨o₂, ho₂, hne₂, ha₂, -⟩ := FreeV.struct ⟨h, ht, hk, by omega, hofree⟩ hl
  obtain ⟨⟨u', hu'o, hu'2, hu'ne⟩, -⟩ := hc o₂ ho₂ hne₂
  exact hu'ne (ha₂ u' hu'2 hu'o)

theorem TwinMuOne_free_twin_col (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (hk : k = 2 * lam + 2)
    (hl : 3 ≤ lam) (x : Fin n) : 2 ≤ (colCl A x).card :=
  TwinMuOne_free_twin (isDSRG_transpose h) ht hk hl x

theorem TwinMuOne_no_family (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (hk : k = 2 * lam + 2)
    (hl : 4 ≤ lam) (hn : 0 < n) : False :=
  TwinMuOne_family h ht hk hl (TwinMuOne_free_twin h ht hk (by omega)) (TwinMuOne_free_twin_col h ht hk (by omega))
    ⟨0, hn⟩

end

theorem TwinMuOne_no_66_10_5_4_1 (A : Mat) : ¬ IsDSRG 66 A 10 5 4 1 := fun h =>
  TwinMuOne_no_family h (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem TwinMuOne_no_91_12_6_5_1 (A : Mat) : ¬ IsDSRG 91 A 12 6 5 1 := fun h =>
  TwinMuOne_no_family h (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end DsrgRank
