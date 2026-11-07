import DsrgRank.TwinClassesMuOne

set_option autoImplicit false

namespace DsrgRank

open Matrix

section

variable {n : Nat} {A : Mat} {k t lam mu : Int}

theorem Twin_card_out (h : IsDSRG n A k t lam mu) (x : Fin n) :
    ((outN A x).card : Int) = k + 1 := by
  have hd : ∑ l : Fin n, delta x l = 1 := by
    simpa using sum_delta_mulTw (fun _ => (1 : Int)) x
  rw [card_eq_sum, Finset.sum_congr rfl (fun l _ => TwinMuOne_ind h x l), Finset.sum_add_distrib, hd]
  have hk := h.2.2.1 x x.isLt
  rw [sumBelow_eq_fin] at hk
  rw [hk]

theorem Twin_card_in (h : IsDSRG n A k t lam mu) (y : Fin n) :
    ((inN A y).card : Int) = k + 1 :=
  Twin_card_out (isDSRG_transpose h) y

theorem Twin_inter (h : IsDSRG n A k t lam mu) (ht : t = lam + 1) (x y : Fin n) :
    ((outN A x ∩ inN A y).card : Int) =
      (lam + 2 - mu) * (if y ∈ outN A x then 1 else 0) + mu := by
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

theorem Twin_inter_out (h : IsDSRG n A k t lam mu) (ht : t = lam + 1) {x y : Fin n}
    (hy : y ∉ outN A x) : ((outN A x ∩ inN A y).card : Int) = mu := by
  have e := Twin_inter h ht x y
  simp only [hy, ite_false, mul_zero, zero_add] at e
  exact e

theorem Twin_inter_in (h : IsDSRG n A k t lam mu) (ht : t = lam + 1) {x y : Fin n}
    (hy : y ∈ outN A x) : ((outN A x ∩ inN A y).card : Int) = lam + 2 := by
  have e := Twin_inter h ht x y
  simp only [hy, ite_true, mul_one] at e
  rw [e]
  ring

theorem Twin_out_eq (h : IsDSRG n A k t lam mu) {x u : Fin n} (hsub : outN A x ⊆ outN A u) :
    outN A x = outN A u := by
  apply Finset.eq_of_subset_of_card_le hsub
  have e1 := Twin_card_out h x
  have e2 := Twin_card_out h u
  omega

theorem Twin_exists_out (h : IsDSRG n A k t lam mu) {x u : Fin n}
    (hne : outN A u ≠ outN A x) : ∃ w ∈ outN A u, w ∉ outN A x := by
  by_contra hc
  apply hne
  apply Twin_out_eq h
  intro w hw
  by_contra hwx
  exact hc ⟨w, hw, hwx⟩

theorem Twin_cl_in {x z : Fin n} (hz : z ∈ outN A x) : rowCl A x ⊆ inN A z := by
  intro c hc
  rw [← out_iff_in, mem_rowCl.1 hc]
  exact hz

theorem Twin_sub (x : Fin n) : rowCl A x ⊆ outN A x ∩ inN A x :=
  fun _ hy => Finset.mem_inter.2 ⟨twin_out hy, twin_in hy⟩

theorem Twin_le (h : IsDSRG n A k t lam mu) (ht : t = lam + 1) (htk : t < k) (x : Fin n) :
    ((rowCl A x).card : Int) ≤ lam + 1 := by
  have hCN : rowCl A x ⊆ outN A x := rowCl_sub_out x
  have hne : (outN A x \ rowCl A x).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hem
    have hNC' : outN A x ⊆ rowCl A x := Finset.sdiff_eq_empty_iff_subset.1 hem
    have hsub : outN A x ⊆ outN A x ∩ inN A x := by
      intro u hu
      exact Finset.mem_inter.2 ⟨hu, Twin_cl_in (self_mem_outN x) (hNC' hu)⟩
    have hle := Finset.card_le_card hsub
    have e1 := Twin_inter_in h ht (self_mem_outN (A := A) x)
    have e2 := Twin_card_out h x
    omega
  obtain ⟨z, hz⟩ := hne
  have hz' := Finset.mem_sdiff.1 hz
  have e1 := Twin_inter_in h ht hz'.1
  have hsub : insert z (rowCl A x) ⊆ outN A x ∩ inN A z := by
    intro u hu
    rcases Finset.mem_insert.1 hu with e | hu
    · rw [e]
      exact Finset.mem_inter.2 ⟨hz'.1, self_mem_inN z⟩
    · exact Finset.mem_inter.2 ⟨hCN hu, Twin_cl_in hz'.1 hu⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hz'.2] at hle
  omega

theorem Twin_gamma (h : IsDSRG n A k t lam mu) (ht : t = lam + 1) {x u : Fin n}
    (hux : u ∉ rowCl A x) : ((outN A u ∩ rowCl A x).card : Int) ≤ mu := by
  have hne : outN A x ≠ outN A u := fun e => hux (mem_rowCl.2 e.symm)
  obtain ⟨w, hwx, hwu⟩ := Twin_exists_out h hne
  have e := Twin_inter_out h ht hwu
  have hsub : outN A u ∩ rowCl A x ⊆ outN A u ∩ inN A w := by
    intro c hc
    have hc' := Finset.mem_inter.1 hc
    exact Finset.mem_inter.2 ⟨hc'.1, Twin_cl_in hwx hc'.2⟩
  have hle := Finset.card_le_card hsub
  rw [← e]
  exact_mod_cast hle

theorem Twin_other (h : IsDSRG n A k t lam mu) (ht : t = lam + 1) {x u : Fin n}
    (hux : u ∉ rowCl A x) : ((rowCl A u ∩ outN A x).card : Int) ≤ mu := by
  have hne : outN A u ≠ outN A x := fun e => hux (mem_rowCl.2 e)
  obtain ⟨w, hwu, hwx⟩ := Twin_exists_out h hne
  have e := Twin_inter_out h ht hwx
  have hsub : rowCl A u ∩ outN A x ⊆ outN A x ∩ inN A w := by
    intro c hc
    have hc' := Finset.mem_inter.1 hc
    exact Finset.mem_inter.2 ⟨hc'.2, Twin_cl_in hwu hc'.1⟩
  have hle := Finset.card_le_card hsub
  rw [← e]
  exact_mod_cast hle

theorem Twin_class (h : IsDSRG n A k t lam mu) (ht : t = lam + 1) (x : Fin n) :
    ((rowCl A x).card : Int) * (lam + 2 - (rowCl A x).card) ≤
      mu * (k + 1 - (rowCl A x).card) := by
  classical
  have hCN : rowCl A x ⊆ outN A x := rowCl_sub_out x
  have hNC : ((outN A x \ rowCl A x).card : Int) = k + 1 - (rowCl A x).card := by
    have e1 := Finset.card_sdiff_add_card_eq_card hCN
    have e2 := Twin_card_out h x
    omega
  have hY : ∀ y ∈ rowCl A x,
      ((((outN A x \ rowCl A x).filter (fun u => u ∈ inN A y)).card : Nat) : Int) =
        lam + 2 - (rowCl A x).card := by
    intro y hy
    have hyN : y ∈ outN A x := hCN hy
    have e1 := Twin_inter_in h ht hyN
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
        · exact ⟨hCN hu, Twin_cl_in hyN hu⟩
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
      ((((rowCl A x).filter (fun y => u ∈ inN A y)).card : Nat) : Int) ≤ mu := by
    intro u hu
    have hux : u ∉ rowCl A x := (Finset.mem_sdiff.1 hu).2
    have hsub : (rowCl A x).filter (fun y => u ∈ inN A y) ⊆ outN A u ∩ rowCl A x := by
      intro y hy
      have hy' := Finset.mem_filter.1 hy
      exact Finset.mem_inter.2 ⟨out_iff_in.2 hy'.2, hy'.1⟩
    have h1 : ((((rowCl A x).filter (fun y => u ∈ inN A y)).card : Nat) : Int) ≤
        (outN A u ∩ rowCl A x).card := by
      exact_mod_cast Finset.card_le_card hsub
    exact h1.trans (Twin_gamma h ht hux)
  have hsum : ((∑ u ∈ outN A x \ rowCl A x,
      ((rowCl A x).filter (fun y => u ∈ inN A y)).card : Nat) : Int) ≤
      mu * (outN A x \ rowCl A x).card := by
    push_cast
    calc ∑ u ∈ outN A x \ rowCl A x,
          ((((rowCl A x).filter (fun y => u ∈ inN A y)).card : Nat) : Int)
          ≤ ∑ _u ∈ outN A x \ rowCl A x, mu := Finset.sum_le_sum hle1
      _ = mu * (outN A x \ rowCl A x).card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hsumY : ((∑ y ∈ rowCl A x,
      ((outN A x \ rowCl A x).filter (fun u => u ∈ inN A y)).card : Nat) : Int) =
      (rowCl A x).card * (lam + 2 - (rowCl A x).card) := by
    push_cast
    rw [Finset.sum_congr rfl hY, Finset.sum_const, nsmul_eq_mul]
  have hc : ((∑ y ∈ rowCl A x,
      ((outN A x \ rowCl A x).filter (fun u => u ∈ inN A y)).card : Nat) : Int) ≤
      mu * (outN A x \ rowCl A x).card := by
    rw [hswap]
    exact hsum
  rw [hsumY, hNC] at hc
  exact hc

theorem Twin_far (h : IsDSRG n A k t lam mu) (ht : t = lam + 1) {x u : Fin n}
    (hux : u ∉ rowCl A x) : lam + 2 - mu ≤ ((outN A u \ outN A x).card : Int) := by
  have hne : outN A u ≠ outN A x := fun e => hux (mem_rowCl.2 e)
  obtain ⟨w, hwu, hwx⟩ := Twin_exists_out h hne
  have e1 := Twin_inter_in h ht hwu
  have e2 := Twin_inter_out h ht hwx
  have hsub : outN A u ∩ inN A w ⊆
      (outN A x ∩ inN A w) ∪ (outN A u \ outN A x) := by
    intro z hz
    have hz' := Finset.mem_inter.1 hz
    by_cases hzx : z ∈ outN A x
    · exact Finset.mem_union.2 (Or.inl (Finset.mem_inter.2 ⟨hzx, hz'.2⟩))
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_sdiff.2 ⟨hz'.1, hzx⟩))
  have h1 := (Finset.card_le_card hsub).trans
    (Finset.card_union_le (outN A x ∩ inN A w) (outN A u \ outN A x))
  have h3 : ((outN A u ∩ inN A w).card : Int) ≤
      (outN A x ∩ inN A w).card + (outN A u \ outN A x).card := by
    exact_mod_cast h1
  linarith

theorem Twin_lower (h : IsDSRG n A k t lam mu) (ht : t = lam + 1) (x : Fin n) :
    (lam + 2 - mu) * (k + 1 - (rowCl A x).card) ≤ mu * ((n : Int) - (k + 1)) := by
  classical
  have hCN : rowCl A x ⊆ outN A x := rowCl_sub_out x
  have hNC : ((outN A x \ rowCl A x).card : Int) = k + 1 - (rowCl A x).card := by
    have e1 := Finset.card_sdiff_add_card_eq_card hCN
    have e2 := Twin_card_out h x
    omega
  have hW : ((Finset.univ \ outN A x).card : Int) = (n : Int) - (k + 1) := by
    have e1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (outN A x))
    have e2 := Twin_card_out h x
    rw [Finset.card_univ, Fintype.card_fin] at e1
    omega
  have hE : ∀ u : Fin n, outN A u \ outN A x =
      (Finset.univ \ outN A x).filter (fun w => w ∈ outN A u) := by
    intro u
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hIn : ∀ w ∈ Finset.univ \ outN A x,
      ((((outN A x \ rowCl A x).filter (fun u => w ∈ outN A u)).card : Nat) : Int) = mu := by
    intro w hw
    have hwx : w ∉ outN A x := (Finset.mem_sdiff.1 hw).2
    have hset : (outN A x \ rowCl A x).filter (fun u => w ∈ outN A u) =
        outN A x ∩ inN A w := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_inter]
      constructor
      · rintro ⟨⟨hu, _⟩, hwu⟩
        exact ⟨hu, out_iff_in.1 hwu⟩
      · rintro ⟨hu, hwu⟩
        refine ⟨⟨hu, ?_⟩, out_iff_in.2 hwu⟩
        intro huC
        apply hwx
        rw [← mem_rowCl.1 huC]
        exact out_iff_in.2 hwu
    rw [hset]
    exact Twin_inter_out h ht hwx
  have hswap : ∑ u ∈ outN A x \ rowCl A x,
      ((Finset.univ \ outN A x).filter (fun w => w ∈ outN A u)).card =
      ∑ w ∈ Finset.univ \ outN A x,
        ((outN A x \ rowCl A x).filter (fun u => w ∈ outN A u)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hlow : ∀ u ∈ outN A x \ rowCl A x, lam + 2 - mu ≤
      ((((Finset.univ \ outN A x).filter (fun w => w ∈ outN A u)).card : Nat) : Int) := by
    intro u hu
    rw [← hE u]
    exact Twin_far h ht (Finset.mem_sdiff.1 hu).2
  have h1 : (lam + 2 - mu) * (outN A x \ rowCl A x).card ≤
      ((∑ u ∈ outN A x \ rowCl A x,
        ((Finset.univ \ outN A x).filter (fun w => w ∈ outN A u)).card : Nat) : Int) := by
    push_cast
    calc (lam + 2 - mu) * ((outN A x \ rowCl A x).card : Int)
        = ∑ _u ∈ outN A x \ rowCl A x, (lam + 2 - mu) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum hlow
  have h2 : ((∑ w ∈ Finset.univ \ outN A x,
        ((outN A x \ rowCl A x).filter (fun u => w ∈ outN A u)).card : Nat) : Int) =
      mu * (Finset.univ \ outN A x).card := by
    push_cast
    rw [Finset.sum_congr rfl hIn, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hswap, h2, hNC, hW] at h1
  exact h1

theorem Twin_upper (h : IsDSRG n A k t lam mu) (ht : t = lam + 1) (htk : t < k) (x : Fin n) :
    ((rowCl A x).card : Int) ≤ k - lam - 1 + mu := by
  classical
  have eQ := Twin_inter_in h ht (self_mem_outN (A := A) x)
  have hle := Twin_le h ht htk x
  have hex : ((outN A x ∩ inN A x) \ rowCl A x).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hem
    have hsub := Finset.sdiff_eq_empty_iff_subset.1 hem
    have := Finset.card_le_card hsub
    omega
  obtain ⟨u, hu⟩ := hex
  have hu' := Finset.mem_sdiff.1 hu
  have huQ := Finset.mem_inter.1 hu'.1
  have hxu : x ∈ outN A u := out_iff_in.2 huQ.2
  have eP := Twin_inter_in h ht hxu
  have hcommon : (outN A u ∩ inN A x) ∩ outN A x =
      (outN A x ∩ inN A x) ∩ outN A u := by
    ext z
    simp only [Finset.mem_inter]
    tauto
  have s1 := Finset.card_sdiff_add_card_inter (outN A u ∩ inN A x) (outN A x)
  have s2 := Finset.card_sdiff_add_card_inter (outN A x ∩ inN A x) (outN A u)
  rw [hcommon] at s1
  have hC : rowCl A x \ outN A u ⊆ (outN A x ∩ inN A x) \ outN A u :=
    Finset.sdiff_subset_sdiff (Twin_sub x) (Finset.Subset.refl _)
  have s3 := Finset.card_sdiff_add_card_inter (rowCl A x) (outN A u)
  have hg : ((rowCl A x ∩ outN A u).card : Int) ≤ mu := by
    rw [Finset.inter_comm]
    exact Twin_gamma h ht hu'.2
  have hPR : (outN A u ∩ inN A x) \ outN A x ⊆ inN A x \ outN A x := by
    intro z hz
    have hz' := Finset.mem_sdiff.1 hz
    exact Finset.mem_sdiff.2 ⟨(Finset.mem_inter.1 hz'.1).2, hz'.2⟩
  have s4 := Finset.card_sdiff_add_card_inter (inN A x) (outN A x)
  rw [Finset.inter_comm (inN A x) (outN A x)] at s4
  have eIn := Twin_card_in h x
  have c1 := Finset.card_le_card hC
  have c2 := Finset.card_le_card hPR
  omega

end

section

variable {n : Nat} {A : Mat} {k t lam mu : Int}

theorem Twin_spec (h : IsDSRG n A k t lam mu) (ht : t = lam + 1) (hq : mu < lam + 2)
    (hμ : mu ≠ 0) (hn : 0 < n) :
    (toR n A - (-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).rank =
        1 + Module.finrank ℝ (eigA n A ((lam : ℝ) + 1 - mu)) ∧
      (lam + 2 - mu) * (Module.finrank ℝ (eigA n A ((lam : ℝ) + 1 - mu)) : Int) = n - 1 - k := by
  have hd : disc t lam mu = (lam + 2 - mu) ^ 2 := by
    unfold disc
    rw [ht]
    ring
  have hpos : 0 < disc t lam mu := by
    rw [hd]
    have h0 : 0 < lam + 2 - mu := by omega
    exact pow_pos h0 2
  have hc : Real.sqrt (disc t lam mu : ℝ) = (lam : ℝ) + 2 - mu := by
    rw [hd]
    push_cast
    have : (0 : ℝ) ≤ (lam : ℝ) + 2 - mu := by
      have : (mu : ℝ) < (lam : ℝ) + 2 := by exact_mod_cast hq
      linarith
    exact Real.sqrt_sq this
  have hrR : rR t lam mu = (lam : ℝ) + 1 - mu := by
    unfold rR
    rw [hc]
    push_cast
    ring
  have hsR : sR t lam mu = -1 := by
    unfold sR
    rw [hc]
    push_cast
    ring
  have hr : IsRootPair t lam mu (-1) ((lam : ℝ) + 1 - mu) := by
    refine ⟨?_, ?_⟩
    · ring
    · rw [ht]
      push_cast
      ring
  refine ⟨rank_sub_root h hn hpos hμ hr, ?_⟩
  obtain ⟨_, _, hsum, htr⟩ := spectrum_counts h hn hpos hμ
  rw [hrR, hsR] at hsum htr
  set f := Module.finrank ℝ (eigA n A ((lam : ℝ) + 1 - mu)) with hf
  set g := Module.finrank ℝ (eigA n A (-1)) with hg
  have hfg : (f : ℝ) + g = (n : ℝ) - 1 := by
    have : ((f + g : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) := by rw [hsum]
    push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne')] at this
    linarith
  have hR : ((lam : ℝ) + 2 - mu) * f = n - 1 - k := by linarith
  exact_mod_cast hR

theorem Twin_admissible (h : IsDSRG n A k t lam mu) (ht : t = lam + 1) (htk : t < k)
    (hq : mu < lam + 2) (hμ : mu ≠ 0) (x : Fin n) :
    ((rowCl A x).card : Int) ≤ lam + 1 ∧
      ((rowCl A x).card : Int) * (lam + 2 - (rowCl A x).card) ≤
        mu * (k + 1 - (rowCl A x).card) ∧
      k + 1 - ((rowCl A x).card : Int) ≤
        mu * (Module.finrank ℝ (eigA n A ((lam : ℝ) + 1 - mu)) : Int) ∧
      ((rowCl A x).card : Int) ≤ k - lam - 1 + mu := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) x.isLt
  have hf := (Twin_spec h ht hq hμ hn).2
  have hlow := Twin_lower h ht x
  refine ⟨Twin_le h ht htk x, Twin_class h ht x, ?_, Twin_upper h ht htk x⟩
  have hq' : 0 < lam + 2 - mu := by omega
  -- `(λ + 2 − μ)(k + 1 − a) ≤ μ(n − 1 − k) = (λ + 2 − μ)·μf`
  have h1 : (lam + 2 - mu) * (k + 1 - (rowCl A x).card) ≤
      (lam + 2 - mu) * (mu * (Module.finrank ℝ (eigA n A ((lam : ℝ) + 1 - mu)) : Int)) := by
    have : mu * ((n : Int) - (k + 1)) =
        (lam + 2 - mu) * (mu * (Module.finrank ℝ (eigA n A ((lam : ℝ) + 1 - mu)) : Int)) := by
      linear_combination (-mu) * hf
    linarith
  exact le_of_mul_le_mul_left h1 hq'

theorem Twin_cond (h : IsDSRG n A k t lam mu) (ht : t = lam + 1) (htk : t < k)
    (hq : mu < lam + 2) (x : Fin n) :
    (lam + 2 - mu) ^ 2 ≤ mu * ((n : Int) - 1 - k) := by
  have hlow := Twin_lower h ht x
  have hup := Twin_upper h ht htk x
  have hq' : 0 ≤ lam + 2 - mu := by omega
  have h1 : lam + 2 - mu ≤ k + 1 - (rowCl A x).card := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hq'
  nlinarith [h2, hlow]

theorem Twin_no_80_19_13_12_2 (A : Mat) : ¬ IsDSRG 80 A 19 13 12 2 := by
  intro h
  have x : Fin 80 := ⟨0, by norm_num⟩
  have h1 := Twin_lower h (by norm_num) x
  have h2 := Twin_upper h (by norm_num) (by norm_num) x
  norm_num at h1 h2
  omega

end

end DsrgRank
