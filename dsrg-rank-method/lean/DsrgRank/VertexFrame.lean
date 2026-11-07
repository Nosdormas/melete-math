import DsrgRank.TwinClassesMuOne

set_option autoImplicit false

namespace DsrgRank

open Matrix

section

variable {n : Nat} {A : Mat} {k t lam : Int}

theorem VFrame_count (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (x o y : Fin n) :
    ((blk A x o ∩ inN A y).card : Int) =
      (lam + 1) * (if y ∈ outN A o then 1 else 0) + 1 -
        (outN A o ∩ outN A x ∩ inN A y).card := by
  have e := TwinMuOne_inter h ht o y
  have hsplit : outN A o ∩ inN A y =
      (blk A x o ∩ inN A y) ∪ (outN A o ∩ outN A x ∩ inN A y) := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_union, mem_blk]
    by_cases hj : j ∈ outN A x <;> simp [hj]
  have hdisj : Disjoint (blk A x o ∩ inN A y) (outN A o ∩ outN A x ∩ inN A y) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    exact (mem_blk.1 (Finset.mem_inter.1 hj1).1).2
      (Finset.mem_inter.1 (Finset.mem_inter.1 hj2).1).2
  rw [hsplit, Finset.card_union_of_disjoint hdisj] at e
  push_cast at e
  linarith

theorem VFrame_blk_card (h : IsDSRG n A k t lam 1) (x o : Fin n) :
    ((blk A x o).card : Int) = k + 1 - (outN A o ∩ outN A x).card := by
  have e1 := Finset.card_sdiff_add_card_inter (outN A o) (outN A x)
  have e2 := TwinMuOne_card_out h o
  unfold blk
  omega

theorem VFrame_blk_ge (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) {x o w : Fin n}
    (ho : o ∈ outN A x) (hw : w ∈ blk A x o) : lam + 1 ≤ ((blk A x o).card : Int) := by
  have e := TwinMuOne_blk_in h ht ho hw
  have hle : (blk A x o ∩ inN A w).card ≤ (blk A x o).card :=
    Finset.card_le_card Finset.inter_subset_left
  omega

theorem VFrame_blk_empty (h : IsDSRG n A k t lam 1) {x o : Fin n} :
    blk A x o = ∅ ↔ o ∈ rowCl A x := by
  constructor
  · intro he
    apply mem_rowCl.2
    apply TwinMuOne_out_eq h
    intro j hj
    by_contra hjx
    have hm : j ∈ blk A x o := mem_blk.2 ⟨hj, hjx⟩
    rw [he] at hm
    simp at hm
  · intro hr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro w hw
    have hw' := mem_blk.1 hw
    apply hw'.2
    rw [← mem_rowCl.1 hr]
    exact hw'.1

theorem VFrame_rowCl_eq (h : IsDSRG n A k t lam 1) (x : Fin n) :
    rowCl A x = (outN A x).filter (fun o => blk A x o = ∅) := by
  ext o
  simp only [Finset.mem_filter]
  rw [VFrame_blk_empty h]
  exact ⟨fun hr => ⟨twin_out hr, hr⟩, fun hr => hr.2⟩

theorem VFrame_indep (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) {x u u' : Fin n}
    (ha : ((rowCl A x).card : Int) = lam + 1)
    (hu : u ∈ outN A x) (hux : u ∉ rowCl A x) (hu' : u' ∈ outN A x)
    (hu'x : u' ∉ rowCl A x) (hin : u ∈ inN A u') : u = u' := by
  by_contra hne
  have e := TwinMuOne_inter_in h ht hu'
  have hsub : insert u (insert u' (rowCl A x)) ⊆ outN A x ∩ inN A u' := by
    intro j hj
    rcases Finset.mem_insert.1 hj with e1 | hj
    · rw [e1]
      exact Finset.mem_inter.2 ⟨hu, hin⟩
    rcases Finset.mem_insert.1 hj with e2 | hj
    · rw [e2]
      exact Finset.mem_inter.2 ⟨hu', self_mem_inN u'⟩
    · refine Finset.mem_inter.2 ⟨twin_out hj, ?_⟩
      rw [← out_iff_in, mem_rowCl.1 hj]
      exact hu'
  have hn2 : u ∉ insert u' (rowCl A x) := by
    rw [Finset.mem_insert]
    rintro (e3 | e3)
    · exact hne e3
    · exact hux e3
  have hle := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hn2, Finset.card_insert_of_notMem hu'x] at hle
  omega

theorem VFrame_col_in_row (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) {x u u' : Fin n}
    (ha : ((rowCl A x).card : Int) = lam + 1)
    (hu : u ∈ outN A x) (hux : u ∉ rowCl A x) (hu' : u' ∈ colCl A u) (hne : u' ≠ u) :
    u' ∈ rowCl A x := by
  by_contra hu'x
  have hu'o : u' ∈ outN A x := TwinMuOne_col_union hu hu'
  have hin : u ∈ inN A u' := by
    rw [mem_colCl.1 hu']
    exact self_mem_inN u
  exact hne (VFrame_indep h ht ha hu hux hu'o hu'x hin).symm

theorem VFrame_colfree (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) {x : Fin n}
    (ha : ((rowCl A x).card : Int) = lam + 1) :
    k + 1 - 2 * (lam + 1) ≤
      (((outN A x \ rowCl A x).filter (fun u => colCl A u = {u})).card : Int) := by
  classical
  have hUc : (((outN A x \ rowCl A x).card : Nat) : Int) = k + 1 - (lam + 1) := by
    have e1 := Finset.card_sdiff_add_card_eq_card (rowCl_sub_out (A := A) x)
    have e2 := TwinMuOne_card_out h x
    omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := outN A x \ rowCl A x)
    (fun u => colCl A u = {u})
  have hpiece : ∀ c ∈ rowCl A x,
      ((outN A x \ rowCl A x).filter (fun u => u ∈ colCl A c)).card ≤ 1 := by
    intro c _
    apply Finset.card_le_one.2
    intro u1 h1 u2 h2
    have a1 := Finset.mem_filter.1 h1
    have a2 := Finset.mem_filter.1 h2
    have m1 := Finset.mem_sdiff.1 a1.1
    have m2 := Finset.mem_sdiff.1 a2.1
    have hc12 : u2 ∈ colCl A u1 := by
      rw [colCl_eq a1.2]
      exact a2.2
    by_contra hne
    exact m2.2 (VFrame_col_in_row h ht ha m1.1 m1.2 hc12 (fun e => hne e.symm))
  have hcover : (outN A x \ rowCl A x).filter (fun u => ¬ colCl A u = {u}) ⊆
      (rowCl A x).biUnion
        (fun c => (outN A x \ rowCl A x).filter (fun u => u ∈ colCl A c)) := by
    intro u hu
    have a := Finset.mem_filter.1 hu
    have m := Finset.mem_sdiff.1 a.1
    obtain ⟨u', hu', hne⟩ : ∃ u' ∈ colCl A u, u' ≠ u := by
      by_contra hc
      push Not at hc
      apply a.2
      rw [Finset.eq_singleton_iff_unique_mem]
      exact ⟨self_mem_colCl u, hc⟩
    have hrow := VFrame_col_in_row h ht ha m.1 m.2 hu' hne
    rw [Finset.mem_biUnion]
    refine ⟨u', hrow, Finset.mem_filter.2 ⟨a.1, ?_⟩⟩
    rw [colCl_eq hu']
    exact self_mem_colCl u
  have hle1 := Finset.card_le_card hcover
  have hle2 : ((rowCl A x).biUnion
      (fun c => (outN A x \ rowCl A x).filter (fun u => u ∈ colCl A c))).card ≤
      ∑ c ∈ rowCl A x, ((outN A x \ rowCl A x).filter (fun u => u ∈ colCl A c)).card :=
    Finset.card_biUnion_le
  have hle3 : ∑ c ∈ rowCl A x,
      ((outN A x \ rowCl A x).filter (fun u => u ∈ colCl A c)).card ≤
      (rowCl A x).card := by
    calc ∑ c ∈ rowCl A x,
          ((outN A x \ rowCl A x).filter (fun u => u ∈ colCl A c)).card
          ≤ ∑ _c ∈ rowCl A x, 1 := Finset.sum_le_sum hpiece
      _ = (rowCl A x).card := by simp
  omega

theorem VFrame_rowfree (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) {x : Fin n}
    (hd : ((colCl A x).card : Int) = lam + 1) :
    k + 1 - 2 * (lam + 1) ≤
      (((inN A x \ colCl A x).filter (fun u => rowCl A u = {u})).card : Int) :=
  VFrame_colfree (isDSRG_transpose h) ht hd

theorem VFrame_no_full (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (htk : t < k)
    (hfree : ∀ y : Fin n, rowCl A y ≠ {y} ∧ colCl A y ≠ {y})
    (hK : 2 * (lam + 1) < k + 1) (x : Fin n) : ((rowCl A x).card : Int) ≤ lam := by
  have hcl := (TwinMuOne_class h ht htk x).2
  by_contra hc
  have ha : ((rowCl A x).card : Int) = lam + 1 := by omega
  have hf := VFrame_colfree h ht ha
  have hpos : 0 < ((outN A x \ rowCl A x).filter (fun u => colCl A u = {u})).card := by
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.1 hpos
  exact (hfree u).2 (Finset.mem_filter.1 hu).2

theorem VFrame_no_full_col (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (htk : t < k)
    (hfree : ∀ y : Fin n, rowCl A y ≠ {y} ∧ colCl A y ≠ {y})
    (hK : 2 * (lam + 1) < k + 1) (x : Fin n) : ((colCl A x).card : Int) ≤ lam :=
  VFrame_no_full (isDSRG_transpose h) ht htk (fun y => ⟨(hfree y).2, (hfree y).1⟩) hK x

theorem VFrame_two_le {x : Fin n} (hne : rowCl A x ≠ {x}) : 2 ≤ (rowCl A x).card := by
  by_contra hc
  apply hne
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨self_mem_rowCl x, fun y hy => ?_⟩
  exact Finset.card_le_one.1 (by omega) y hy x (self_mem_rowCl x)

theorem VFrame_even {x : Fin n} (h2 : ∀ u ∈ outN A x, (colCl A u).card = 2) :
    Even (outN A x).card := by
  classical
  have hfib : ∀ c ∈ (outN A x).image (colCl A),
      ((outN A x).filter (fun y => colCl A y = c)).card = 2 := by
    intro c hc
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hc
    have heq : (outN A x).filter (fun y => colCl A y = colCl A u) = colCl A u := by
      ext y
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨_, e⟩
        rw [← e]
        exact self_mem_colCl y
      · intro hy
        exact ⟨TwinMuOne_col_union hu hy, colCl_eq hy⟩
    rw [heq]
    exact h2 u hu
  rw [Finset.card_eq_sum_card_image (colCl A) (outN A x), Finset.sum_congr rfl hfib,
    Finset.sum_const, smul_eq_mul]
  exact ⟨((outN A x).image (colCl A)).card, by ring⟩

theorem VFrame_pairs (h : IsDSRG n A k t lam 1) (ht : t = lam + 1) (htk : t < k) (hl : lam = 2)
    (hfree : ∀ y : Fin n, rowCl A y ≠ {y} ∧ colCl A y ≠ {y}) (hK : 6 < k + 1) (x : Fin n) :
    (rowCl A x).card = 2 ∧ (colCl A x).card = 2 ∧ Even (k + 1) := by
  have hK' : 2 * (lam + 1) < k + 1 := by omega
  have hr : ∀ y : Fin n, (rowCl A y).card = 2 := by
    intro y
    have e1 := VFrame_no_full h ht htk hfree hK' y
    have e2 := VFrame_two_le (hfree y).1
    omega
  have hc : ∀ y : Fin n, (colCl A y).card = 2 := by
    intro y
    have e1 := VFrame_no_full_col h ht htk hfree hK' y
    have e2 := VFrame_two_le (A := transpose A) (hfree y).2
    have e3 : (rowCl (transpose A) y).card = (colCl A y).card := rfl
    omega
  refine ⟨hr x, hc x, ?_⟩
  obtain ⟨r, hr'⟩ := VFrame_even (A := A) (x := x) (fun u _ => hc u)
  have e := TwinMuOne_card_out h x
  exact ⟨(r : Int), by omega⟩

end

theorem VFrame_28 (A : Mat) (h : IsDSRG 28 A 6 3 2 1) :
    ∃ y : Fin 28, rowCl A y = {y} ∨ colCl A y = {y} := by
  by_contra hc
  push Not at hc
  have hp := VFrame_pairs h (by norm_num) (by norm_num) rfl hc (by norm_num) ⟨0, by norm_num⟩
  obtain ⟨r, hr⟩ := hp.2.2
  omega

theorem VFrame_70 (A : Mat) (h : IsDSRG 70 A 9 3 2 1)
    (hfree : ∀ y : Fin 70, rowCl A y ≠ {y} ∧ colCl A y ≠ {y}) (x : Fin 70) :
    (rowCl A x).card = 2 ∧ (colCl A x).card = 2 := by
  have hp := VFrame_pairs h (by norm_num) (by norm_num) rfl hfree (by norm_num) x
  exact ⟨hp.1, hp.2.1⟩

end DsrgRank
