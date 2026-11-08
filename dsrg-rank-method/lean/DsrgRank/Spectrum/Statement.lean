module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.Real.Sqrt
public import DsrgRank.Spectrum.Defs

/-!
Defines the statements of the spectral lemma: the rational and real forms toQ and toR, the image and
kernel of D(A), the eigenspaces eigA, the roots rR and sR, and the predicates SpectralLemmaStruct,
SpectralLemmaStmt and SpectralLemmaFull.
-/

@[expose] public section

namespace DsrgRank

open Matrix

def toQ (n : Nat) (M : Mat) : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => (M i j : ℚ)

def toR (n : Nat) (M : Mat) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (M i j : ℝ)

def SpectralLemmaStmt (n : Nat) (A : Mat) (k t lam mu : Int) : Prop :=
  RankBound n k t lam mu (toQ n (D A)).rank ∧
  (2 * (n : Int) * kappa k t) ^ 2 ≤ ((toQ n (D A)).rank : Int) * traceDDt2 n A

def imD (n : Nat) (A : Mat) : Submodule ℝ (Fin n → ℝ) := LinearMap.range (toR n (D A)).mulVecLin

def kerD (n : Nat) (A : Mat) : Submodule ℝ (Fin n → ℝ) := LinearMap.ker (toR n (D A)).mulVecLin

def eigA (n : Nat) (A : Mat) (x : ℝ) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker (toR n A - x • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVecLin

noncomputable def rR (t lam mu : Int) : ℝ := (((lam - mu : ℤ) : ℝ) + Real.sqrt (disc t lam mu)) / 2

noncomputable def sR (t lam mu : Int) : ℝ := (((lam - mu : ℤ) : ℝ) - Real.sqrt (disc t lam mu)) / 2

def SpectralLemmaStruct (n : Nat) (A : Mat) (t lam mu : Int) : Prop :=
  (∀ x ∈ imD n A, (fun _ => (1 : ℝ)) ⬝ᵥ x = 0) ∧
  (∀ x ∈ imD n A, toR n A *ᵥ x ∈ imD n A) ∧
  (∀ x ∈ imD n A, (toR n A)ᵀ *ᵥ x ∈ imD n A) ∧
  (∃ m : ℕ, (toQ n (D A)).rank = 2 * m ∧
    Module.finrank ℝ ↥(imD n A ⊓ eigA n A (rR t lam mu)) = m ∧
    Module.finrank ℝ ↥(imD n A ⊓ eigA n A (sR t lam mu)) = m ∧
    imD n A = imD n A ⊓ eigA n A (rR t lam mu) ⊔ imD n A ⊓ eigA n A (sR t lam mu)) ∧
  (∀ x ∈ kerD n A, toR n A *ᵥ x ∈ kerD n A) ∧
  (∀ x ∈ kerD n A, (toR n A)ᵀ *ᵥ x ∈ kerD n A) ∧
  (∀ x ∈ kerD n A, toR n A *ᵥ x = (toR n A)ᵀ *ᵥ x)

def SpectralLemmaFull (n : Nat) (A : Mat) (k t lam mu : Int) : Prop :=
  SpectralLemmaStruct n A t lam mu ∧ SpectralLemmaStmt n A k t lam mu

end DsrgRank
