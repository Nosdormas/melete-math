module

public import DsrgRank.Parts

/-!
Defines the discriminant disc = (lambda - mu)^2 + 4(t - mu), the predicate RankBound n k t lambda mu
R (R at most n - 1 and (2k + (n - 1)(lambda - mu))^2 at most (n - 1 - R)^2 disc), and traceDDt2, the
trace of (D D^T)^2 for the skew part D of A.
-/

@[expose] public section

namespace DsrgRank

def disc (t lam mu : Int) : Int := (lam - mu) ^ 2 + 4 * (t - mu)

def RankBound (n : Nat) (k t lam mu : Int) (R : Nat) : Prop :=
  (R : Int) ≤ (n : Int) - 1 ∧
  (2 * k + ((n : Int) - 1) * (lam - mu)) ^ 2 ≤ ((n : Int) - 1 - R) ^ 2 * disc t lam mu

instance (n : Nat) (k t lam mu : Int) (R : Nat) : Decidable (RankBound n k t lam mu R) := by
  unfold RankBound; infer_instance

def traceDDt2 (n : Nat) (A : Mat) : Int :=
  sumBelow n fun i =>
    mul n (mul n (D A) (transpose (D A))) (mul n (D A) (transpose (D A))) i i

end DsrgRank
