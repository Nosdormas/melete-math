module

public import DsrgRank.DSRG

/-!
Defines the integer matrix vocabulary of the rank argument: products and transposes of matrices
indexed by naturals, the two-cycle matrix U, the one-way part N and the skew part D = N - N
transposed, the fixed entries of a partial matrix, and the branch conditions NoCycle3, NoTriangle
and PathsMutual with their layout cells.
-/

@[expose] public section

namespace DsrgRank

abbrev Mat := Nat → Nat → Int

def transpose (M : Mat) : Mat := fun i j => M j i

def mul (n : Nat) (M P : Mat) : Mat := fun i j => sumBelow n (fun l => M i l * P l j)

def kappa (k t : Int) : Int := k - t

def U (A : Mat) : Mat := fun i j => A i j * A j i

def N (A : Mat) : Mat := fun i j => A i j - U A i j

def D (A : Mat) : Mat := fun i j => N A i j - N A j i

abbrev Fix := List (Nat × Nat × Int)

def Agrees (A : Mat) (F : Fix) : Prop := ∀ c ∈ F, A c.1 c.2.1 = c.2.2

instance (A : Mat) (F : Fix) : Decidable (Agrees A F) := by
  unfold Agrees; infer_instance

inductive Branch
  | cycle
  | tt
  | z
  | r
  deriving DecidableEq, Repr

def NoCycle3 (n : Nat) (A : Mat) : Prop :=
  ∀ x, x < n → ∀ y, y < n → ∀ w, w < n → ¬ (N A x y = 1 ∧ N A y w = 1 ∧ N A w x = 1)

instance (n : Nat) (A : Mat) : Decidable (NoCycle3 n A) := by
  unfold NoCycle3; infer_instance

def NoTriangle (n : Nat) (A : Mat) : Prop :=
  NoCycle3 n A ∧
  ∀ x, x < n → ∀ y, y < n → ∀ w, w < n → ¬ (N A x y = 1 ∧ N A x w = 1 ∧ N A y w = 1)

instance (n : Nat) (A : Mat) : Decidable (NoTriangle n A) := by
  unfold NoTriangle; infer_instance

def PathsMutual (n : Nat) (A : Mat) : Prop :=
  ∀ x, x < n → ∀ y, y < n → ∀ w, w < n → (N A x y = 1 ∧ N A y w = 1) → A x w = 1 ∧ A w x = 1

instance (n : Nat) (A : Mat) : Decidable (PathsMutual n A) := by
  unfold PathsMutual; infer_instance

def BranchGlobal (b : Branch) (n : Nat) (A : Mat) : Prop :=
  match b with
  | .cycle => True
  | .tt => NoCycle3 n A
  | .z => NoTriangle n A
  | .r => NoTriangle n A ∧ PathsMutual n A

instance (b : Branch) (n : Nat) (A : Mat) : Decidable (BranchGlobal b n A) := by
  cases b <;> unfold BranchGlobal <;> infer_instance

def layoutCells (n k t : Nat) : Fix :=
  (List.range n).flatMap fun y =>
    if y = 0 then []
    else [(0, y, if y ≤ k then 1 else 0),
          (y, 0, if y ≤ t ∨ (k < y ∧ y ≤ 2 * k - t) then 1 else 0)]

def arcCells (x y : Nat) : Fix := [(x, y, 1), (y, x, 0)]

def branchCells (n k t : Nat) : Branch → Fix
  | .cycle => layoutCells n k t ++ arcCells (t + 1) (k + 1)
  | .tt => layoutCells n k t ++ arcCells (t + 1) (t + 2)
  | .z => layoutCells n k t ++ arcCells (t + 1) (2 * k - t + 1)
  | .r => layoutCells n k t

def swap (a b i : Nat) : Nat := if i = a then b else if i = b then a else i

def swapMat (a b : Nat) (A : Mat) : Mat := fun i j => A (swap a b i) (swap a b j)

def ofRows (rows : List (List Int)) : Mat := fun i j => (rows.getD i []).getD j 0

end DsrgRank
