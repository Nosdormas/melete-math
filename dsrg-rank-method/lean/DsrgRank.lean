module

public import DsrgRank.Spectral
public import DsrgRank.KernelFrame
public import DsrgRank.LocalRank
public import DsrgRank.ClosedNeighbourhood
public import DsrgRank.LeftKernel
public import DsrgRank.SchurComplement
public import DsrgRank.ProfileBound
public import DsrgRank.VertexRecovery
public import DsrgRank.TwinClassesMuOne
public import DsrgRank.TwinClasses
public import DsrgRank.VertexFrame
public import DsrgRank.Complement
public import DsrgRank.Case28
public import DsrgRank.LeftKernelComponents
public import DsrgRank.Graphs.Small

/-!
# Nonexistence of directed strongly regular graphs by rank arguments

Root of the library. A directed strongly regular graph with parameters `(v, k, t, λ, μ)` is a 0-1
matrix `A` with `IsDSRG v A k t λ μ` (module `DsrgRank.DSRG`). Every theorem of the form
`∀ A : Mat, ¬ IsDSRG v A k t λ μ` in the imported modules excludes one parameter set; the list of
these theorems is `theorem_names` in `comparator.json`, and `Challenge.lean` states them with
Mathlib alone.
-/

@[expose] public section

