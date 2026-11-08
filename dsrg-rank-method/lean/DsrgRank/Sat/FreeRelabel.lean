module

public import DsrgRank.TwinClassesMuOne
public import DsrgRank.Sat.FreeLink
public import DsrgRank.Sat.TrieCheck
import all Std.Sat.CNF.Sat

/-!
Relabels a DSRG with a vertex whose row twin class is a single vertex into canonical form and counts
the classes of the other vertices. It proves that a clause list which passes checkNat and is
unsatisfiable rules out such a DSRG (no_free_of_checked_unsat).
-/

@[expose] public section

set_option autoImplicit false

namespace DsrgRank.Sat.Free

open DsrgRank DsrgRank.Sat.Card

section Relabel

variable {v k t lam mu : Nat} {A : Mat}

theorem card_fin_filter (v : Nat) (p : Nat → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun j : Fin v => p j.val)).card = ((Finset.range v).filter p).card := by
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext j
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a.isLt, ha⟩
  · rintro ⟨hj, hp⟩; exact ⟨⟨j, hj⟩, hp, rfl⟩

theorem card_range_Ioc {v a b : Nat} (hb : b < v) :
    ((Finset.range v).filter (fun j => a < j ∧ j ≤ b)).card = b - a := by
  have : (Finset.range v).filter (fun j => a < j ∧ j ≤ b) = Finset.Ioc a b := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]; omega
  rw [this, Nat.card_Ioc]

def newCls (k t j : Nat) : Nat :=
  if j = 0 then 0 else if j ≤ t then 1 else if j ≤ k then 2 else if j ≤ 2 * k - t then 3 else 4

noncomputable def oldCls (A : Mat) (x z : Nat) : Nat :=
  if z = x then 0 else if A x z = 1 ∧ A z x = 1 then 1 else if A x z = 1 then 2
  else if A z x = 1 then 3 else 4

theorem newCls_le (j : Nat) : newCls k t j ≤ 4 := by
  unfold newCls; split_ifs <;> omega

theorem oldCls_le (x z : Nat) : oldCls A x z ≤ 4 := by
  unfold oldCls; split_ifs <;> omega

theorem card_eq_of_sum {p : Fin v → Prop} [DecidablePred p] {f : Fin v → Int}
    (hf : ∀ z, f z = if p z then 1 else 0) {c : Int} (hs : ∑ z, f z = c) :
    ((Finset.univ.filter p).card : Int) = c := by
  rw [← hs, Finset.sum_congr rfl (fun z _ => hf z), Finset.sum_boole]

theorem card_old (h : IsDSRG v A k t lam mu) (x : Fin v) (c : Nat) (hc : c < 4) :
    (Finset.univ.filter (fun z : Fin v => oldCls A x z = c)).card =
      if c = 0 then 1 else if c = 1 then t else k - t := by
  obtain ⟨h01, hdiag, hrow, hcol, hsq⟩ := h
  have hxx := hdiag x x.isLt
  have hout : ((Finset.univ.filter (fun z : Fin v => A x z = 1)).card : Int) = k := by
    have := hrow x x.isLt
    rw [sumBelow_eq_fin] at this
    refine card_eq_of_sum (f := fun z : Fin v => A x z) (fun z => ?_) this
    rcases h01 x x.isLt z z.isLt with e | e <;> simp [e]
  have hin : ((Finset.univ.filter (fun z : Fin v => A z x = 1)).card : Int) = k := by
    have := hcol x x.isLt
    rw [sumBelow_eq_fin] at this
    refine card_eq_of_sum (f := fun z : Fin v => A z x) (fun z => ?_) this
    rcases h01 z z.isLt x x.isLt with e | e <;> simp [e]
  have hmut : ((Finset.univ.filter (fun z : Fin v => A x z = 1 ∧ A z x = 1)).card : Int) = t := by
    have := hsq x x.isLt x x.isLt
    simp only [delta, ite_true, hxx] at this
    rw [sumBelow_eq_fin] at this
    refine card_eq_of_sum (f := fun z : Fin v => A x z * A z x) (fun z => ?_) (by rw [this]; ring)
    rcases h01 x x.isLt z z.isLt with e | e <;> rcases h01 z z.isLt x x.isLt with e' | e' <;>
      simp [e, e']
  have hne : ∀ z : Fin v, A x z = 1 → (z : Nat) ≠ x := fun z e he => by
    rw [show (z : Nat) = x from he] at e; omega
  have hne' : ∀ z : Fin v, A z x = 1 → (z : Nat) ≠ x := fun z e he => by
    rw [show (z : Nat) = x from he] at e; omega
  have hsplit_out := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun z : Fin v => A x z = 1)) (fun z => A z x = 1)
  have hsplit_in := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun z : Fin v => A z x = 1)) (fun z => A x z = 1)
  simp only [Finset.filter_filter] at hsplit_out hsplit_in
  interval_cases c
  · simp only [ite_true]
    have : Finset.univ.filter (fun z : Fin v => oldCls A x z = 0) = {x} := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]; unfold oldCls
      constructor
      · intro hz; split_ifs at hz with h1; exact Fin.ext h1
      · rintro rfl; simp
    rw [this, Finset.card_singleton]
  · simp only [show (1 : Nat) ≠ 0 from by omega, ite_false, ite_true]
    have : Finset.univ.filter (fun z : Fin v => oldCls A x z = 1) =
        Finset.univ.filter (fun z : Fin v => A x z = 1 ∧ A z x = 1) := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; unfold oldCls
      constructor
      · intro hz; split_ifs at hz <;> first | assumption | omega
      · intro hz; simp [hne z hz.1, hz]
    rw [this]; exact_mod_cast hmut
  · simp only [show (2 : Nat) ≠ 0 from by omega, show (2 : Nat) ≠ 1 from by omega, ite_false]
    have : Finset.univ.filter (fun z : Fin v => oldCls A x z = 2) =
        Finset.univ.filter (fun z : Fin v => A x z = 1 ∧ ¬ A z x = 1) := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; unfold oldCls
      constructor
      · intro hz; split_ifs at hz <;> omega
      · intro hz; simp [hne z hz.1, hz]
    rw [this]
    have hm : (Finset.univ.filter (fun z : Fin v => A x z = 1 ∧ A z x = 1)).card = t := by
      exact_mod_cast hmut
    have ho : (Finset.univ.filter (fun z : Fin v => A x z = 1)).card = k := by exact_mod_cast hout
    omega
  · simp only [show (3 : Nat) ≠ 0 from by omega, show (3 : Nat) ≠ 1 from by omega, ite_false]
    have : Finset.univ.filter (fun z : Fin v => oldCls A x z = 3) =
        Finset.univ.filter (fun z : Fin v => A z x = 1 ∧ ¬ A x z = 1) := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; unfold oldCls
      constructor
      · intro hz; split_ifs at hz <;> omega
      · intro hz; simp [hne' z hz.1, hz]
    rw [this]
    have hm : (Finset.univ.filter (fun z : Fin v => A z x = 1 ∧ A x z = 1)).card = t := by
      have e : Finset.univ.filter (fun z : Fin v => A z x = 1 ∧ A x z = 1) =
          Finset.univ.filter (fun z : Fin v => A x z = 1 ∧ A z x = 1) := by
        ext z; simp [and_comm]
      rw [e]; exact_mod_cast hmut
    have hi : (Finset.univ.filter (fun z : Fin v => A z x = 1)).card = k := by exact_mod_cast hin
    omega

theorem card_new (htk : t ≤ k) (hv : 2 * k - t < v) (c : Nat) (hc : c < 4) :
    (Finset.univ.filter (fun j : Fin v => newCls k t j = c)).card =
      if c = 0 then 1 else if c = 1 then t else k - t := by
  rw [card_fin_filter v (fun j => newCls k t j = c)]
  interval_cases c
  · have : (Finset.range v).filter (fun j => newCls k t j = 0) = {0} := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; unfold newCls
      constructor
      · rintro ⟨_, hj⟩; split_ifs at hj; omega
      · rintro rfl; simp; omega
    rw [this]; rfl
  · show _ = t
    have e := card_range_Ioc (v := v) (a := 0) (b := t) (by omega)
    rw [Nat.sub_zero] at e
    rw [← e]
    · congr 1; ext j; simp only [Finset.mem_filter, Finset.mem_range]; unfold newCls
      constructor
      · rintro ⟨h1, hj⟩; split_ifs at hj <;> omega
      · rintro ⟨h1, h2, h3⟩; refine ⟨h1, ?_⟩; split_ifs <;> omega
  · show _ = k - t
    rw [← card_range_Ioc (v := v) (a := t) (b := k) (by omega)]
    congr 1; ext j; simp only [Finset.mem_filter, Finset.mem_range]; unfold newCls
    constructor
    · rintro ⟨h1, hj⟩; split_ifs at hj <;> omega
    · rintro ⟨h1, h2, h3⟩; refine ⟨h1, ?_⟩; split_ifs <;> omega
  · show _ = k - t
    have e := card_range_Ioc (v := v) (a := k) (b := 2 * k - t) (by omega)
    rw [show 2 * k - t - k = k - t by omega] at e
    rw [← e]
    congr 1; ext j; simp only [Finset.mem_filter, Finset.mem_range]; unfold newCls
    constructor
    · rintro ⟨h1, hj⟩; split_ifs at hj <;> omega
    · rintro ⟨h1, h2, h3⟩; refine ⟨h1, ?_⟩; split_ifs <;> omega

theorem sum_cls_card (g : Fin v → Nat) (hg : ∀ z, g z ≤ 4) :
    ∑ c ∈ Finset.range 5, (Finset.univ.filter (fun z : Fin v => g z = c)).card = v := by
  have := Finset.card_eq_sum_card_fiberwise (f := g) (s := Finset.univ) (t := Finset.range 5)
    (fun z _ => Finset.mem_range.2 (by have := hg z; omega))
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact this.symm

theorem card_cls_eq (h : IsDSRG v A k t lam mu) (x : Fin v) (htk : t ≤ k) (hv : 2 * k - t < v)
    (c : Nat) : (Finset.univ.filter (fun j : Fin v => newCls k t j = c)).card =
      (Finset.univ.filter (fun z : Fin v => oldCls A x z = c)).card := by
  by_cases hc : c < 4
  · rw [card_new htk hv c hc, card_old h x c hc]
  · by_cases h4 : c = 4
    · subst h4
      have e1 := sum_cls_card (v := v) (fun j => newCls k t j) (fun j => newCls_le j)
      have e2 := sum_cls_card (v := v) (fun z => oldCls A x z) (fun z => oldCls_le x z)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e1 e2
      rw [card_new htk hv 0 (by omega), card_new htk hv 1 (by omega), card_new htk hv 2 (by omega),
        card_new htk hv 3 (by omega)] at e1
      rw [card_old h x 0 (by omega), card_old h x 1 (by omega), card_old h x 2 (by omega),
        card_old h x 3 (by omega)] at e2
      simp only [ite_true, show (1 : Nat) ≠ 0 from by omega, show (2 : Nat) ≠ 0 from by omega,
        show (3 : Nat) ≠ 0 from by omega, show (2 : Nat) ≠ 1 from by omega,
        show (3 : Nat) ≠ 1 from by omega, ite_false] at e1 e2
      omega
    · have e1 : Finset.univ.filter (fun j : Fin v => newCls k t j = c) = ∅ := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]; have := newCls_le (k := k) (t := t) j; omega
      have e2 : Finset.univ.filter (fun z : Fin v => oldCls A x z = c) = ∅ := by
        ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]; have := oldCls_le (A := A) x z; omega
      rw [e1, e2]

theorem t_le_k (h : IsDSRG v A k t lam mu) (x : Fin v) : t ≤ k := by
  have e1 := card_old h x 1 (by omega)
  simp only [show (1 : Nat) ≠ 0 from by omega, ite_false, ite_true] at e1
  have : Finset.univ.filter (fun z : Fin v => oldCls A x z = 1) ⊆
      Finset.univ.filter (fun z : Fin v => oldCls A x z = 1 ∨ oldCls A x z = 2) := by
    intro z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Or.inl
  have e2 := card_old h x 2 (by omega)
  simp only [show (2 : Nat) ≠ 0 from by omega, show (2 : Nat) ≠ 1 from by omega, ite_false] at e2
  have hout : (Finset.univ.filter (fun z : Fin v => A x z = 1)).card = k := by
    have := h.2.2.1 x x.isLt
    rw [sumBelow_eq_fin] at this
    have e := card_eq_of_sum (p := fun z : Fin v => A x z = 1) (f := fun z => A x z) (fun z => by
      rcases h.1 x x.isLt z z.isLt with e | e <;> simp [e]) this
    exact_mod_cast e
  have hsub : Finset.univ.filter (fun z : Fin v => oldCls A x z = 1) ⊆
      Finset.univ.filter (fun z : Fin v => A x z = 1) := by
    intro z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; unfold oldCls
    intro hz; split_ifs at hz with h1 h2 <;> omega
  have := Finset.card_le_card hsub
  omega

theorem two_k_lt (h : IsDSRG v A k t lam mu) (x : Fin v) : 2 * k - t < v := by
  have htk := t_le_k h x
  have e0 := card_old h x 0 (by omega)
  have e1 := card_old h x 1 (by omega)
  have e2 := card_old h x 2 (by omega)
  have e3 := card_old h x 3 (by omega)
  simp only [ite_true, show (1 : Nat) ≠ 0 from by omega, show (2 : Nat) ≠ 0 from by omega,
    show (3 : Nat) ≠ 0 from by omega, show (2 : Nat) ≠ 1 from by omega,
    show (3 : Nat) ≠ 1 from by omega, ite_false] at e0 e1 e2 e3
  have e := sum_cls_card (v := v) (fun z => oldCls A x z) (fun z => oldCls_le x z)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e
  omega

theorem oldCls_out {x z : Nat} (hz : z ≠ x) : A x z = 1 ↔ (oldCls A x z = 1 ∨ oldCls A x z = 2) := by
  unfold oldCls
  by_cases h2 : A x z = 1 <;> by_cases h3 : A z x = 1 <;> simp [hz, h2, h3]

theorem oldCls_in {x z : Nat} (hz : z ≠ x) : A z x = 1 ↔ (oldCls A x z = 1 ∨ oldCls A x z = 3) := by
  unfold oldCls
  by_cases h2 : A x z = 1 <;> by_cases h3 : A z x = 1 <;> simp [hz, h2, h3]

theorem newCls_out {j : Nat} (hj : 0 < j) (htk : t ≤ k) :
    (newCls k t j = 1 ∨ newCls k t j = 2) ↔ j ≤ k := by
  unfold newCls; split_ifs <;> omega

theorem newCls_in {j : Nat} (hj : 0 < j) (htk : t ≤ k) :
    (newCls k t j = 1 ∨ newCls k t j = 3) ↔ (j ≤ t ∨ (k < j ∧ j ≤ 2 * k - t)) := by
  unfold newCls; split_ifs <;> omega

theorem relabel_canonical (h : IsDSRG v A k t lam mu) (x : Fin v) (hx : rowCl A x = {x}) :
    ∃ A' : Mat, IsDSRG v A' k t lam mu ∧
      (∀ j, 0 < j → j < v →
        (A' 0 j = 1 ↔ j ≤ k) ∧ (A' j 0 = 1 ↔ (j ≤ t ∨ (k < j ∧ j ≤ 2 * k - t)))) ∧
      (∀ y, 0 < y → y < v → A' y 0 = 1 → A' 0 y = 1 →
        ∃ j, 0 < j ∧ j < v ∧ j ≠ y ∧ ¬ (A' y j = 1 ↔ A' 0 j = 1)) := by
  classical
  have htk := t_le_k h x
  have hv := two_k_lt h x
  have hcard := card_cls_eq h x htk hv
  let e : ∀ c, {j : Fin v // newCls k t j = c} ≃ {z : Fin v // oldCls A x z = c} := fun c =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact hcard c)
  let f : Fin v ≃ Fin v := Equiv.ofFiberEquiv e
  have hf : ∀ j, oldCls A x (f j) = newCls k t j := fun j => Equiv.ofFiberEquiv_map e j
  let A' : Mat := fun i j => if hi : i < v then if hj : j < v then A (f ⟨i, hi⟩) (f ⟨j, hj⟩) else 0 else 0
  have hA' : ∀ i j : Fin v, A' i j = A (f i) (f j) := fun i j => by simp [A', i.isLt, j.isLt]
  have hv0 : 0 < v := by have := x.isLt; omega
  have hf0 : f ⟨0, hv0⟩ = x := by
    have := hf ⟨0, hv0⟩
    simp only [newCls, ite_true, oldCls] at this
    split_ifs at this with h1
    exact Fin.ext h1
  obtain ⟨h01, hdiag, hrow, hcol, hsq⟩ := h
  have hsum : ∀ g : Fin v → Int, ∑ j, g (f j) = ∑ z, g z := fun g => Equiv.sum_comp f g
  have hdelta : ∀ i j : Fin v, delta (f i) (f j) = delta i j := by
    intro i j; simp only [delta]
    by_cases hij : i = j
    · subst hij; simp
    · have : (f i : Nat) ≠ f j := fun e' => hij (f.injective (Fin.ext e'))
      have : (i : Nat) ≠ j := fun e' => hij (Fin.ext e')
      simp_all
  refine ⟨A', ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i hi j hj
    rw [hA' ⟨i, hi⟩ ⟨j, hj⟩]
    exact h01 _ (f ⟨i, hi⟩).isLt _ (f ⟨j, hj⟩).isLt
  · intro i hi
    rw [hA' ⟨i, hi⟩ ⟨i, hi⟩]
    exact hdiag _ (f ⟨i, hi⟩).isLt
  · intro i hi
    have hc := hrow _ (f ⟨i, hi⟩).isLt
    rw [sumBelow_eq_fin] at hc ⊢
    rw [Finset.sum_congr rfl (fun j _ => hA' ⟨i, hi⟩ j), hsum (fun z => A (f ⟨i, hi⟩) z)]
    exact hc
  · intro j hj
    have hc := hcol _ (f ⟨j, hj⟩).isLt
    rw [sumBelow_eq_fin] at hc ⊢
    rw [Finset.sum_congr rfl (fun i _ => hA' i ⟨j, hj⟩), hsum (fun z => A z (f ⟨j, hj⟩))]
    exact hc
  · intro i hi j hj
    have hc := hsq _ (f ⟨i, hi⟩).isLt _ (f ⟨j, hj⟩).isLt
    rw [sumBelow_eq_fin] at hc ⊢
    rw [Finset.sum_congr rfl (fun l _ => by rw [hA' ⟨i, hi⟩ l, hA' l ⟨j, hj⟩]),
      hsum (fun z => A (f ⟨i, hi⟩) z * A z (f ⟨j, hj⟩)), hc, hA' ⟨i, hi⟩ ⟨j, hj⟩]
    have := hdelta ⟨i, hi⟩ ⟨j, hj⟩
    simp only at this
    rw [this]
  · intro j h0 hj
    have hfj := hf ⟨j, hj⟩
    have hne : (f ⟨j, hj⟩ : Nat) ≠ x := by
      intro he
      have : f ⟨j, hj⟩ = f ⟨0, hv0⟩ := by rw [hf0]; exact Fin.ext he
      have := congrArg Fin.val (f.injective this)
      simp at this; omega
    rw [show (0 : Nat) = ((⟨0, hv0⟩ : Fin v) : Nat) from rfl, hA' ⟨0, hv0⟩ ⟨j, hj⟩,
      hA' ⟨j, hj⟩ ⟨0, hv0⟩, hf0, oldCls_out hne, oldCls_in hne, hfj]
    exact ⟨newCls_out h0 htk, newCls_in h0 htk⟩
  · intro y h0 hy hy0 h0y
    by_contra hc
    push Not at hc
    have hmem : f ⟨y, hy⟩ ∈ rowCl A x := by
      rw [mem_rowCl]
      ext z
      obtain ⟨j, rfl⟩ := f.surjective z
      rw [mem_outN, mem_outN]
      rw [show (0 : Nat) = ((⟨0, hv0⟩ : Fin v) : Nat) from rfl, hA' ⟨y, hy⟩ ⟨0, hv0⟩, hf0] at hy0
      rw [show (0 : Nat) = ((⟨0, hv0⟩ : Fin v) : Nat) from rfl, hA' ⟨0, hv0⟩ ⟨y, hy⟩, hf0] at h0y
      by_cases hj0 : (j : Nat) = 0
      · have : j = ⟨0, hv0⟩ := Fin.ext hj0
        subst this; rw [hf0]; simp [hy0]
      · by_cases hjy : (j : Nat) = y
        · have : j = ⟨y, hy⟩ := Fin.ext hjy
          subst this; simp [h0y]
        · have hjv := j.isLt
          have key := hc j (by omega) hjv hjy
          rw [show (y : Nat) = ((⟨y, hy⟩ : Fin v) : Nat) from rfl, hA' ⟨y, hy⟩ j,
            show (0 : Nat) = ((⟨0, hv0⟩ : Fin v) : Nat) from rfl, hA' ⟨0, hv0⟩ j, hf0] at key
          have n1 : f j ≠ f ⟨y, hy⟩ := fun e' => hjy (congrArg Fin.val (f.injective e'))
          have n2 : f j ≠ x := by
            rw [← hf0]; exact fun e' => hj0 (congrArg Fin.val (f.injective e'))
          simp only [n1, n2, false_or]
          exact key
    rw [hx, Finset.mem_singleton, ← hf0] at hmem
    have := congrArg Fin.val (f.injective hmem)
    simp at this; omega

theorem exists_sat_formula (h : IsDSRG v A k t lam mu) (x : Fin v) (hx : rowCl A x = {x}) :
    ∃ σ : FVar → Bool, ∀ c ∈ formula ⟨v, k, t, lam, mu⟩, clTrue σ c = true := by
  obtain ⟨A', hA', hcan, hfree⟩ := relabel_canonical h x hx
  exact ⟨sigma (boolMat A'), formula_sat (fits_of_dsrg hA' hcan hfree)⟩

theorem exists_sat_checked (h : IsDSRG v A k t lam mu) (x : Fin v) (hx : rowCl A x = {x})
    (cls : List (List (Nat × Bool))) (hc : cls.all (checkNat ⟨v, k, t, lam, mu⟩) = true) :
    ∃ σ : Nat → Bool, ∀ c ∈ cls, (c.any fun l => σ l.1 == l.2) = true := by
  obtain ⟨A', hA', hcan, hfree⟩ := relabel_canonical h x hx
  refine ⟨fun n => sigma (boolMat A') (dec ⟨v, k, t, lam, mu⟩ (n + 1)), fun c hcm => ?_⟩
  exact checkNat_sound (fits_of_dsrg hA' hcan hfree) (List.all_eq_true.1 hc c hcm)

theorem eval_ofLists {a : Nat → Bool} {cls : List (List (Nat × Bool))}
    (h : ∀ c ∈ cls, (c.any fun l => a l.1 == l.2) = true) :
    Std.Sat.CNF.eval a (DsrgRank.Sat.ofLists cls) = true := by
  simp only [DsrgRank.Sat.ofLists, Std.Sat.CNF.eval, Array.all_eq_true_iff_forall_mem, List.mem_toArray,
    List.mem_map]
  rintro _ ⟨c, hc, rfl⟩
  simpa [Std.Sat.CNF.Clause.eval, Std.Sat.CNF.Clause.literals_ofLiterals] using h c hc

theorem no_free_of_checked_unsat (h : IsDSRG v A k t lam mu) (cls : List (List (Nat × Bool)))
    (hc : cls.all (checkNat ⟨v, k, t, lam, mu⟩) = true) (hu : (DsrgRank.Sat.ofLists cls).Unsat)
    (x : Fin v) : rowCl A x ≠ {x} := by
  intro hx
  obtain ⟨σ, hσ⟩ := exists_sat_checked h x hx cls hc
  have e1 := eval_ofLists hσ
  rw [hu σ] at e1
  exact Bool.false_ne_true e1

end Relabel

end DsrgRank.Sat.Free
