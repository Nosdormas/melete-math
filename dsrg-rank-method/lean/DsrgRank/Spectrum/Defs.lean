import DsrgRank.Parts

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
