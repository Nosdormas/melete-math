module

public import Mathlib.Data.Int.Init

/-!
# Challenge: nonexistence of directed strongly regular graphs

A directed strongly regular graph with parameters `(v, k, t, λ, μ)` is a directed graph on `v`
vertices whose adjacency matrix `A` has entries 0 and 1, zero diagonal, every row and column sum
equal to `k`, and `A² = t I + λ A + μ (J − I − A)`, where `J` is the all-ones matrix: every vertex
has `k` out-arcs and `k` in-arcs, `t` of them in two-cycles, and the number of directed paths of
length two from `x` to `y ≠ x` is `λ` when `x → y` is an arc and `μ` otherwise.

A matrix is a function `Nat → Nat → Int`; only its entries with both indices below `v` matter.
Each theorem below states that no such graph exists for one parameter set. The last group are the
complementary parameter sets `(v, v − k − 1, v − 2k + t − 1, v − 2k + μ − 2, v − 2k + λ)` of
excluded sets. The proofs are in the library `DsrgRank` of this project; this file imports Mathlib
only, and its definitions repeat those of `DsrgRank.Sum`, `DsrgRank.DSRG` and `DsrgRank.Parts`
word for word.
-/

@[expose] public section

namespace DsrgRank

/-- `sumBelow n f = f 0 + f 1 + … + f (n − 1)`, the sum of the first `n` values of an integer
sequence; `sumBelow 0 f = 0`. -/
def sumBelow : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumBelow n f + f n

/-- The Kronecker delta: `delta i j = 1` if `i = j` and `0` otherwise. -/
def delta (i j : Nat) : Int := if i = j then 1 else 0

/-- `IsDSRG n A k t lam mu`: restricted to the indices below `n`, the matrix `A` is the adjacency
matrix of a directed strongly regular graph with parameters `(n, k, t, lam, mu)`. The five
conditions say: every entry is `0` or `1`; the diagonal is zero; every row sum is `k`; every column
sum is `k`; and the entry `(i, j)` of `A²` equals `t` on the diagonal, `lam` where `A i j = 1` and
`mu` where `i ≠ j` and `A i j = 0`, that is, `A² = t I + lam A + mu (J − I − A)`. -/
def IsDSRG (n : Nat) (A : Nat → Nat → Int) (k t lam mu : Int) : Prop :=
  (∀ i, i < n → ∀ j, j < n → A i j = 0 ∨ A i j = 1) ∧
  (∀ i, i < n → A i i = 0) ∧
  (∀ i, i < n → sumBelow n (fun j => A i j) = k) ∧
  (∀ j, j < n → sumBelow n (fun i => A i j) = k) ∧
  (∀ i, i < n → ∀ j, j < n →
    sumBelow n (fun l => A i l * A l j) =
      t * delta i j + lam * A i j + mu * (1 - delta i j - A i j))

/-- Integer matrices indexed by natural numbers: `A i j` is the entry in row `i` and column `j`. -/
abbrev Mat := Nat → Nat → Int

-- λ = 0: the rank of the closed neighbourhood of a vertex.

theorem ClosedNbhd_no_50_11_7_0_3 : ∀ A : Mat, ¬ IsDSRG 50 A 11 7 0 3 := sorry
theorem ClosedNbhd_no_54_13_9_0_4 : ∀ A : Mat, ¬ IsDSRG 54 A 13 9 0 4 := sorry
theorem ClosedNbhd_no_64_17_13_0_6 : ∀ A : Mat, ¬ IsDSRG 64 A 17 13 0 6 := sorry
theorem ClosedNbhd_no_68_13_7_0_3 : ∀ A : Mat, ¬ IsDSRG 68 A 13 7 0 3 := sorry
theorem ClosedNbhd_no_70_15_9_0_4 : ∀ A : Mat, ¬ IsDSRG 70 A 15 9 0 4 := sorry
theorem ClosedNbhd_no_78_19_13_0_6 : ∀ A : Mat, ¬ IsDSRG 78 A 19 13 0 6 := sorry
theorem ClosedNbhd_no_88_23_17_0_8 : ∀ A : Mat, ¬ IsDSRG 88 A 23 17 0 8 := sorry
theorem ClosedNbhd_no_100_16_7_0_3 : ∀ A : Mat, ¬ IsDSRG 100 A 16 7 0 3 := sorry
theorem ClosedNbhd_no_108_19_9_0_4 : ∀ A : Mat, ¬ IsDSRG 108 A 19 9 0 4 := sorry
theorem ClosedNbhd_no_110_31_25_0_12 : ∀ A : Mat, ¬ IsDSRG 110 A 31 25 0 12 := sorry

-- λ = 1 and t = 2μ: the components of the out-neighbourhood of a vertex.

theorem LeftKer_no_55_16_12_1_6 : ∀ A : Mat, ¬ IsDSRG 55 A 16 12 1 6 := sorry

-- μ = 1 and t = λ + 1: classes of vertices with equal rows of A + I.

theorem TwinMuOne_no_40_9_6_5_1 : ∀ A : Mat, ¬ IsDSRG 40 A 9 6 5 1 := sorry
theorem TwinMuOne_no_66_10_5_4_1 : ∀ A : Mat, ¬ IsDSRG 66 A 10 5 4 1 := sorry
theorem TwinMuOne_no_91_12_6_5_1 : ∀ A : Mat, ¬ IsDSRG 91 A 12 6 5 1 := sorry
theorem TwinMuOne_no_96_15_10_9_1 : ∀ A : Mat, ¬ IsDSRG 96 A 15 10 9 1 := sorry

-- t = λ + 1: the size of a class of vertices with equal rows of A + I.

theorem Twin_no_80_19_13_12_2 : ∀ A : Mat, ¬ IsDSRG 80 A 19 13 12 2 := sorry

-- (28, 6, 3, 2, 1) and its complementary set: vertex frames and a refutation checked by the kernel.

theorem Case28_no_28_6_3_2_1 : ∀ A : Mat, ¬ IsDSRG 28 A 6 3 2 1 := sorry
theorem Case28_no_28_21_18_15_18 : ∀ A : Mat, ¬ IsDSRG 28 A 21 18 15 18 := sorry

-- Complementary parameter sets of excluded sets.

theorem compl_no_40_30_27_21_27 : ∀ A : Mat, ¬ IsDSRG 40 A 30 27 21 27 := sorry
theorem compl_no_50_38_34_29_28 : ∀ A : Mat, ¬ IsDSRG 50 A 38 34 29 28 := sorry
theorem compl_no_55_38_34_27_24 : ∀ A : Mat, ¬ IsDSRG 55 A 38 34 27 24 := sorry
theorem compl_no_66_55_50_45_50 : ∀ A : Mat, ¬ IsDSRG 66 A 55 50 45 50 := sorry
theorem compl_no_68_54_48_43_42 : ∀ A : Mat, ¬ IsDSRG 68 A 54 48 43 42 := sorry
theorem compl_no_80_60_54_42_54 : ∀ A : Mat, ¬ IsDSRG 80 A 60 54 42 54 := sorry
theorem compl_no_91_78_72_66_72 : ∀ A : Mat, ¬ IsDSRG 91 A 78 72 66 72 := sorry
theorem compl_no_96_80_75_65_75 : ∀ A : Mat, ¬ IsDSRG 96 A 80 75 65 75 := sorry
theorem compl_no_100_83_74_69_68 : ∀ A : Mat, ¬ IsDSRG 100 A 83 74 69 68 := sorry
theorem compl_no_108_88_78_72_70 : ∀ A : Mat, ¬ IsDSRG 108 A 88 78 72 70 := sorry

end DsrgRank
