module

public import Std.Sat.CNF

/-!
Proves that a CNF is unsatisfiable as soon as a sub-formula, made of some of its clauses, is
unsatisfiable (unsat_of_subset).
-/

@[expose] public section

namespace DsrgRank.Sat

open Std.Sat

theorem unsat_of_subset {α : Type} {C F : CNF α} (h : ∀ c ∈ C.clauses, c ∈ F.clauses)
    (hC : C.Unsat) : F.Unsat := by
  intro a
  cases hF : CNF.eval a F with
  | false => rfl
  | true =>
    have hCa : CNF.eval a C = true := by
      simp only [CNF.eval, Array.all_eq_true_iff_forall_mem] at hF ⊢
      exact fun c hc => hF c (h c hc)
    rw [hC a] at hCa
    exact absurd hCa (by simp)

end DsrgRank.Sat
