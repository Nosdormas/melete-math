module

public import DsrgRank.Spectrum.Defs

/-!
Defines the certificate predicates of the spectral lemma: FactorCert, a factorisation of D(A)
through R terms with nonzero integer denominator; MinorCert, a nonzero minor certificate;
SpectralLemmaCert; and SpectralLemmaHalfRefutation, a minor certificate together with the failure of
the doubled rank bound.
-/

@[expose] public section

namespace DsrgRank

def FactorCert (n R : Nat) (M B C : Mat) (d : Int) : Prop :=
  d ≠ 0 ∧ ∀ i, i < n → ∀ j, j < n → d * M i j = sumBelow R (fun l => B i l * C l j)

instance (n R : Nat) (M B C : Mat) (d : Int) : Decidable (FactorCert n R M B C d) := by
  unfold FactorCert; infer_instance

def MinorCert (n R : Nat) (M P Q : Mat) (d : Int) : Prop :=
  d ≠ 0 ∧ ∀ a, a < R → ∀ b, b < R →
    sumBelow n (fun i => P a i * sumBelow n (fun j => M i j * Q j b)) = d * delta a b

instance (n R : Nat) (M P Q : Mat) (d : Int) : Decidable (MinorCert n R M P Q d) := by
  unfold MinorCert; infer_instance

def SpectralLemmaCert (n : Nat) (A : Mat) (k t lam mu : Int)
    (R₁ : Nat) (B C : Mat) (d₁ : Int) (R₂ : Nat) (P Q : Mat) (d₂ : Int) : Prop :=
  FactorCert n R₁ (D A) B C d₁ ∧ MinorCert n R₂ (D A) P Q d₂ ∧
  RankBound n k t lam mu R₁ ∧ 0 ≤ disc t lam mu ∧
  0 ≤ traceDDt2 n A ∧ (2 * (n : Int) * kappa k t) ^ 2 ≤ (R₂ : Int) * traceDDt2 n A

instance (n : Nat) (A : Mat) (k t lam mu : Int) (R₁ : Nat) (B C : Mat) (d₁ : Int) (R₂ : Nat)
    (P Q : Mat) (d₂ : Int) : Decidable (SpectralLemmaCert n A k t lam mu R₁ B C d₁ R₂ P Q d₂) := by
  unfold SpectralLemmaCert; infer_instance

def SpectralLemmaHalfRefutation (n : Nat) (A : Mat) (k t lam mu : Int) (R₂ : Nat) (P Q : Mat) (d₂ : Int) :
    Prop :=
  MinorCert n R₂ (D A) P Q d₂ ∧ 0 ≤ disc t lam mu ∧ ¬ RankBound n k t lam mu (2 * R₂)

instance (n : Nat) (A : Mat) (k t lam mu : Int) (R₂ : Nat) (P Q : Mat) (d₂ : Int) :
    Decidable (SpectralLemmaHalfRefutation n A k t lam mu R₂ P Q d₂) := by
  unfold SpectralLemmaHalfRefutation; infer_instance

end DsrgRank
