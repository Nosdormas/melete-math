module

public import DsrgRank.Complement
public import DsrgRank.Sat.FreeRelabel
public import DsrgRank.Sat.Case28Free

/-!
Proves that no directed strongly regular graph with parameters (28, 6, 3, 2, 1) exists, by reducing
to a vertex whose row twin class is a single vertex and refuting the SAT formula of that case by
kernel evaluation. Its complement with parameters (28, 21, 18, 15, 18) is excluded too.
-/

@[expose] public section

namespace DsrgRank

open DsrgRank.Sat.Free

set_option maxRecDepth 100000 in

theorem Case28_core_checked :
    DsrgRank.Sat.Case28Free.clauses.all (checkNat ⟨28, 6, 3, 2, 1⟩) = true := by
  decide +kernel

theorem Case28_no_28_6_3_2_1 (A : Mat) : ¬ IsDSRG 28 A 6 3 2 1 := by
  intro h
  obtain ⟨B, hB, y, hy⟩ := Case28_free_row A h
  exact no_free_of_checked_unsat (v := 28) (k := 6) (t := 3) (lam := 2) (mu := 1) hB
    DsrgRank.Sat.Case28Free.clauses Case28_core_checked DsrgRank.Sat.Case28Free.formula_unsat y hy

theorem Case28_no_28_21_18_15_18 (A : Mat) : ¬ IsDSRG 28 A 21 18 15 18 := by
  have h := not_isDSRG_compl Case28_no_28_6_3_2_1 A
  norm_num at h
  exact h

end DsrgRank
