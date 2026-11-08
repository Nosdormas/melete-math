module

public import DsrgRank.Sat.LRATCatcher.Kernel
import all Std.Sat.CNF.Sat

/-!
Defines a checker for clause proofs that uses unit propagation and RUP steps, with clauses kept in a
binary trie indexed by natural numbers. It proves checkTrie_sound: when the check passes, the clause
list is unsatisfiable.
-/

@[expose] public section

namespace DsrgRank.Sat

open Std.Sat Std.Tactic.BVDecide.LRAT LRATCatcher

inductive Trie (β : Type) where
  | leaf : Trie β
  | node : Option β → Trie β → Trie β → Trie β

theorem beq_eq_decide (a b : Nat) : Nat.beq a b = decide (a = b) := by
  cases h : Nat.beq a b
  · exact (decide_eq_false (Nat.ne_of_beq_eq_false h)).symm
  · exact (decide_eq_true (Nat.eq_of_beq_eq_true h)).symm

theorem cond_decide' {α : Type} (p : Prop) [Decidable p] (a b : α) :
    cond (decide p) a b = if p then a else b := by
  by_cases h : p <;> simp [h]

noncomputable section

namespace Trie

variable {β : Type}

def root (t : Trie β) : Option β := Trie.rec (motive := fun _ => Option β) none (fun v _ _ _ _ => v) t

def left (t : Trie β) : Trie β := Trie.rec (motive := fun _ => Trie β) leaf (fun _ l _ _ _ => l) t

def right (t : Trie β) : Trie β := Trie.rec (motive := fun _ => Trie β) leaf (fun _ _ r _ _ => r) t

def find (t : Trie β) : Nat → Option β :=
  Trie.rec (motive := fun _ => Nat → Option β) (fun _ => none)
    (fun v _ _ fl fr k =>
      cond (Nat.beq k 0) v
        (cond (Nat.beq (Nat.mod k 2) 1) (fl (Nat.div k 2)) (fr (Nat.sub (Nat.div k 2) 1)))) t

def insert (n : Nat) : Trie β → Nat → β → Trie β :=
  Nat.rec (motive := fun _ => Trie β → Nat → β → Trie β) (fun t _ _ => t)
    (fun _ ih t k b =>
      cond (Nat.beq k 0) (node (some b) (left t) (right t))
        (cond (Nat.beq (Nat.mod k 2) 1) (node (root t) (ih (left t) (Nat.div k 2) b) (right t))
          (node (root t) (left t) (ih (right t) (Nat.sub (Nat.div k 2) 1) b)))) n

theorem find_eq (t : Trie β) (k : Nat) :
    find t k = if k = 0 then root t
      else if k % 2 = 1 then find (left t) (k / 2) else find (right t) (k / 2 - 1) := by
  cases t with
  | leaf =>
    show none = _
    simp only [root, left, right]
    split
    · rfl
    · split <;> rfl
  | node v l r =>
    show cond (Nat.beq k 0) v
      (cond (Nat.beq (Nat.mod k 2) 1) (find l (Nat.div k 2)) (find r (Nat.sub (Nat.div k 2) 1))) = _
    simp only [beq_eq_decide, cond_decide']
    rfl

theorem insert_succ (n : Nat) (t : Trie β) (k : Nat) (b : β) :
    insert (n + 1) t k b = if k = 0 then node (some b) (left t) (right t)
      else if k % 2 = 1 then node (root t) (insert n (left t) (k / 2) b) (right t)
      else node (root t) (left t) (insert n (right t) (k / 2 - 1) b) := by
  show cond (Nat.beq k 0) (node (some b) (left t) (right t))
    (cond (Nat.beq (Nat.mod k 2) 1) (node (root t) (insert n (left t) (Nat.div k 2) b) (right t))
      (node (root t) (left t) (insert n (right t) (Nat.sub (Nat.div k 2) 1) b))) = _
  rw [beq_eq_decide, beq_eq_decide, cond_decide', cond_decide']
  rfl

theorem find_node (v : Option β) (l r : Trie β) (k : Nat) :
    find (node v l r) k = if k = 0 then v
      else if k % 2 = 1 then find l (k / 2) else find r (k / 2 - 1) := by
  rw [find_eq]; rfl

theorem find_insert {b c : β} : ∀ (n : Nat) (t : Trie β) (k w : Nat),
    find (insert n t k b) w = some c → (w = k ∧ c = b) ∨ find t w = some c
  | 0, t, k, w, h => Or.inr h
  | n + 1, t, k, w, h => by
    rw [find_eq t w]
    rw [insert_succ] at h
    by_cases hk : k = 0
    · simp only [hk, ite_true, find_node] at h
      by_cases hw : w = 0
      · simp only [hw, ite_true, Option.some.injEq] at h
        exact Or.inl ⟨hw.trans hk.symm, h.symm⟩
      · simp only [hw, ite_false] at h ⊢
        exact Or.inr h
    · simp only [hk, ite_false] at h
      by_cases hk2 : k % 2 = 1
      · simp only [hk2, ite_true, find_node] at h
        by_cases hw : w = 0
        · simp only [hw, ite_true] at h ⊢
          exact Or.inr h
        · simp only [hw, ite_false] at h ⊢
          by_cases hw2 : w % 2 = 1
          · simp only [hw2, ite_true] at h ⊢
            rcases find_insert n (left t) (k / 2) (w / 2) h with ⟨he, hc⟩ | hr
            · exact Or.inl ⟨by omega, hc⟩
            · exact Or.inr hr
          · simp only [hw2, ite_false] at h ⊢
            exact Or.inr h
      · simp only [hk2, ite_false, find_node] at h
        by_cases hw : w = 0
        · simp only [hw, ite_true] at h ⊢
          exact Or.inr h
        · simp only [hw, ite_false] at h ⊢
          by_cases hw2 : w % 2 = 1
          · simp only [hw2, ite_true] at h ⊢
            exact Or.inr h
          · simp only [hw2, ite_false] at h ⊢
            rcases find_insert n (right t) (k / 2 - 1) (w / 2 - 1) h with ⟨he, hc⟩ | hr
            · exact Or.inl ⟨by omega, hc⟩
            · exact Or.inr hr

end Trie

def depth : Nat := 64

abbrev TDB := Trie KClause

abbrev TAsg := Trie Bool

def DBSat (a : Nat → Bool) (db : TDB) : Prop :=
  ∀ k c, db.find k = some c → clauseTrue a c = true

def AgreesT (a : Nat → Bool) (α : TAsg) : Prop :=
  ∀ v b, α.find v = some b → a v = b

theorem dbSat_insert {a : Nat → Bool} {db : TDB} {k : Nat} {c : KClause}
    (h : DBSat a db) (hc : clauseTrue a c = true) : DBSat a (db.insert depth k c) := by
  intro w d hd
  rcases Trie.find_insert depth db k w hd with ⟨_, rfl⟩ | hr
  · exact hc
  · exact h w d hr

theorem agreesT_insert {a : Nat → Bool} {α : TAsg} {v : Nat} {b : Bool}
    (h : AgreesT a α) (hv : a v = b) : AgreesT a (α.insert depth v b) := by
  intro w c hw
  rcases Trie.find_insert depth α v w hw with ⟨rfl, rfl⟩ | hr
  · exact hv
  · exact h w c hr

def litValT (α : TAsg) (l : Literal Nat) : Option Bool :=
  Option.rec none (fun b => some (b == l.2)) (α.find l.1)

theorem ne_of_litValT {a : Nat → Bool} {α : TAsg} {l : Literal Nat}
    (hag : AgreesT a α) (h : litValT α l = some false) : a l.1 ≠ l.2 := by
  unfold litValT at h
  cases hf : α.find l.1 with
  | none => rw [hf] at h; cases h
  | some b =>
    rw [hf] at h
    have hb : (b == l.2) = false := Option.some.inj h
    rw [hag _ _ hf]
    intro heq
    rw [heq] at hb
    simp at hb

def litEq (l m : Literal Nat) : Bool := Nat.beq l.1 m.1 && (l.2 == m.2)

theorem eq_of_litEq {l m : Literal Nat} (h : litEq l m = true) : l = m := by
  obtain ⟨l1, l2⟩ := l
  obtain ⟨m1, m2⟩ := m
  simp only [litEq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [Nat.eq_of_beq_eq_true h1, h2]

inductive Scan where
  | none_
  | one (l : Literal Nat)
  | many
  | sat

def scan (α : TAsg) (d : KClause) : Scan :=
  List.rec (motive := fun _ => Scan) .none_
    (fun l _ ih =>
      Option.rec
        (Scan.rec (.one l) (fun m => cond (litEq l m) (.one m) .many) .many .sat ih)
        (fun b => cond b .sat ih) (litValT α l)) d

theorem scan_cons (α : TAsg) (l : Literal Nat) (d : KClause) :
    scan α (l :: d) = Option.rec
      (Scan.rec (.one l) (fun m => cond (litEq l m) (.one m) .many) .many .sat (scan α d))
      (fun b => cond b .sat (scan α d)) (litValT α l) := rfl

theorem scan_none {α : TAsg} : ∀ {d : KClause}, scan α d = .none_ →
    ∀ l ∈ d, litValT α l = some false
  | [], _, l, hl => by cases hl
  | l :: d, h, l', hl' => by
    rw [scan_cons] at h
    cases hv : litValT α l with
    | none =>
      rw [hv] at h
      cases hs : scan α d with
      | none_ => rw [hs] at h; cases h
      | one m =>
        rw [hs] at h
        dsimp only at h
        cases hb : litEq l m <;> rw [hb] at h <;> cases h
      | many => rw [hs] at h; cases h
      | sat => rw [hs] at h; cases h
    | some b =>
      rw [hv] at h
      cases b with
      | true => cases h
      | false =>
        rcases List.mem_cons.mp hl' with rfl | hd
        · exact hv
        · exact scan_none h l' hd

theorem scan_one {α : TAsg} {u : Literal Nat} : ∀ {d : KClause}, scan α d = .one u →
    ∀ l ∈ d, l ≠ u → litValT α l = some false
  | [], h, _, _, _ => by cases h
  | l :: d, h, l', hl', hne => by
    rw [scan_cons] at h
    cases hv : litValT α l with
    | none =>
      rw [hv] at h
      cases hs : scan α d with
      | none_ =>
        rw [hs] at h
        cases h
        rcases List.mem_cons.mp hl' with rfl | hd
        · exact absurd rfl hne
        · exact scan_none hs l' hd
      | one m =>
        rw [hs] at h
        dsimp only at h
        cases hb : litEq l m with
        | false => rw [hb] at h; cases h
        | true =>
          rw [hb] at h
          cases h
          rcases List.mem_cons.mp hl' with rfl | hd
          · exact absurd (eq_of_litEq hb) hne
          · exact scan_one hs l' hd hne
      | many => rw [hs] at h; cases h
      | sat => rw [hs] at h; cases h
    | some b =>
      rw [hv] at h
      cases b with
      | true => cases h
      | false =>
        rcases List.mem_cons.mp hl' with rfl | hd
        · exact hv
        · exact scan_one h l' hd hne

def propagate (db : TDB) (hs : List Nat) : TAsg → Bool :=
  List.rec (motive := fun _ => TAsg → Bool) (fun _ => false)
    (fun h _ ih α =>
      Option.rec false
        (fun d => Scan.rec true (fun l => ih (α.insert depth l.1 l.2)) false (ih α) (scan α d))
        (db.find h)) hs

theorem propagate_cons (db : TDB) (h : Nat) (hs : List Nat) (α : TAsg) :
    propagate db (h :: hs) α = Option.rec false
      (fun d => Scan.rec true (fun l => propagate db hs (α.insert depth l.1 l.2)) false
        (propagate db hs α) (scan α d)) (db.find h) := rfl

theorem propagate_sound {db : TDB} {a : Nat → Bool} (hdb : DBSat a db) :
    ∀ {hs : List Nat} {α : TAsg}, propagate db hs α = true → AgreesT a α → False
  | [], _, h, _ => by cases h
  | h :: hs, α, hp, hag => by
    rw [propagate_cons] at hp
    cases hf : db.find h with
    | none => rw [hf] at hp; cases hp
    | some d =>
      rw [hf] at hp
      dsimp only at hp
      have hsat := hdb h d hf
      obtain ⟨l, hl, hal⟩ := clauseTrue_iff.mp hsat
      cases hsc : scan α d with
      | none_ => exact ne_of_litValT hag (scan_none hsc l hl) hal
      | one u =>
        rw [hsc] at hp
        apply propagate_sound hdb hp
        apply agreesT_insert hag
        by_cases hlu : l = u
        · subst hlu; exact hal
        · exact absurd hal (ne_of_litValT hag (scan_one hsc l hl hlu))
      | many => rw [hsc] at hp; cases hp
      | sat => rw [hsc] at hp; exact propagate_sound hdb hp hag

def assignNeg (c : KClause) : TAsg → TAsg :=
  List.rec (motive := fun _ => TAsg → TAsg) (fun α => α)
    (fun l _ ih α => ih (α.insert depth l.1 (!l.2))) c

theorem agreesT_assignNeg {a : Nat → Bool} :
    ∀ {c : KClause} {α : TAsg}, (∀ l ∈ c, a l.1 ≠ l.2) → AgreesT a α →
      AgreesT a (assignNeg c α)
  | [], _, _, hag => hag
  | l :: ls, α, hc, hag => by
    show AgreesT a (assignNeg ls (α.insert depth l.1 (!l.2)))
    apply agreesT_assignNeg (fun l' hl' => hc l' (List.mem_cons_of_mem _ hl'))
    apply agreesT_insert hag
    have := hc l (List.mem_cons_self ..)
    cases h : a l.1 <;> cases h2 : l.2 <;> simp_all

def rupOK (db : TDB) (c : KClause) (hints : List Nat) : Bool :=
  propagate db hints (assignNeg c .leaf)

theorem rupOK_sound {db : TDB} {c : KClause} {hints : List Nat} {a : Nat → Bool}
    (h : rupOK db c hints = true) (hdb : DBSat a db) : clauseTrue a c = true := by
  cases hc : clauseTrue a c
  · exact (propagate_sound hdb h (agreesT_assignNeg (clauseTrue_eq_false_iff.mp hc)
      (fun _ _ hk => by cases hk))).elim
  · rfl

def checkSteps (proof : List IntAction) : TDB → Bool :=
  List.rec (motive := fun _ => TDB → Bool) (fun _ => false)
    (fun act _ ih db =>
      Action.rec (motive := fun _ => Bool)
        (fun _ hints => rupOK db [] hints.toList)
        (fun id c hints => rupOK db (toKClause c) hints.toList &&
          ih (db.insert depth id (toKClause c)))
        (fun _ _ _ _ _ => false)
        (fun _ => ih db) act) proof

theorem checkSteps_sound {a : Nat → Bool} :
    ∀ {proof : List IntAction} {db : TDB}, checkSteps proof db = true → ¬ DBSat a db
  | [], _, h, _ => by cases h
  | .addEmpty _ hints :: _, db, h, hdb => by
    have := rupOK_sound (show rupOK db [] hints.toList = true from h) hdb
    cases this
  | .addRup id c hints :: rest, db, h, hdb => by
    have h' : (rupOK db (toKClause c) hints.toList &&
        checkSteps rest (db.insert depth id (toKClause c))) = true := h
    simp only [Bool.and_eq_true] at h'
    exact checkSteps_sound h'.2 (dbSat_insert hdb (rupOK_sound h'.1 hdb))
  | .addRat .. :: _, _, h, _ => by cases h
  | .del _ :: rest, db, h, hdb => checkSteps_sound (show checkSteps rest db = true from h) hdb

def initDB (cs : List KClause) : Nat → TDB → TDB :=
  List.rec (motive := fun _ => Nat → TDB → TDB) (fun _ db => db)
    (fun c _ ih i db => ih (i + 1) (db.insert depth i c)) cs

theorem dbSat_initDB {a : Nat → Bool} :
    ∀ {cs : List KClause} {i : Nat} {db : TDB},
      (∀ c ∈ cs, clauseTrue a c = true) → DBSat a db → DBSat a (initDB cs i db)
  | [], _, _, _, hdb => hdb
  | c :: cs, i, db, hcs, hdb => by
    show DBSat a (initDB cs (i + 1) (db.insert depth i c))
    apply dbSat_initDB (fun d hd => hcs d (List.mem_cons_of_mem _ hd))
    exact dbSat_insert hdb (hcs c (List.mem_cons_self ..))

def checkTrie (cls : List KClause) (proof : List IntAction) : Bool :=
  checkSteps proof (initDB cls 1 .leaf)

end

def ofLists (cls : List KClause) : CNF Nat := ⟨(cls.map CNF.Clause.ofLiterals).toArray⟩

theorem checkTrie_sound (cls : List KClause) (proof : List IntAction)
    (h : checkTrie cls proof = true) : (ofLists cls).Unsat := by
  intro a
  cases heval : CNF.eval a (ofLists cls) with
  | false => rfl
  | true =>
    exfalso
    refine checkSteps_sound (a := a) h (dbSat_initDB ?_ (fun _ _ hk => by cases hk))
    intro c hc
    simp only [ofLists, CNF.eval, Array.all_eq_true_iff_forall_mem] at heval
    have hmem : CNF.Clause.ofLiterals c ∈ (cls.map CNF.Clause.ofLiterals).toArray := by
      simp only [List.mem_toArray, List.mem_map]
      exact ⟨c, hc, rfl⟩
    have := heval _ hmem
    simpa [CNF.Clause.eval, clauseTrue, CNF.Clause.literals_ofLiterals] using this

end DsrgRank.Sat
