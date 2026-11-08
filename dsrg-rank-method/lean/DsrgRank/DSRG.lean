module

public import DsrgRank.Sum

/-!
Defines IsDSRG n A k t lambda mu for a 0-1 matrix A of size n: zero diagonal, all row and column
sums equal to k, and A squared equal to t times the identity plus lambda times A plus mu times (J -
I - A). It also defines the Kronecker delta and ofBitmasks, which builds a matrix from row bitmasks.
-/

@[expose] public section

namespace DsrgRank

def delta (i j : Nat) : Int := if i = j then 1 else 0

def IsDSRG (n : Nat) (A : Nat → Nat → Int) (k t lam mu : Int) : Prop :=
  (∀ i, i < n → ∀ j, j < n → A i j = 0 ∨ A i j = 1) ∧
  (∀ i, i < n → A i i = 0) ∧
  (∀ i, i < n → sumBelow n (fun j => A i j) = k) ∧
  (∀ j, j < n → sumBelow n (fun i => A i j) = k) ∧
  (∀ i, i < n → ∀ j, j < n →
    sumBelow n (fun l => A i l * A l j) =
      t * delta i j + lam * A i j + mu * (1 - delta i j - A i j))

instance (n : Nat) (A : Nat → Nat → Int) (k t lam mu : Int) :
    Decidable (IsDSRG n A k t lam mu) := by
  unfold IsDSRG; infer_instance

def ofBitmasks (rows : List Nat) (i j : Nat) : Int :=
  if (rows.getD i 0).testBit j then 1 else 0

end DsrgRank
