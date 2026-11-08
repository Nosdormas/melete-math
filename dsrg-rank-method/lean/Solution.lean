module

public import DsrgRank

/-!
# Solution

The proved counterparts of the statements in `Challenge.lean`. Every theorem named in
`comparator.json` is a theorem of the library `DsrgRank` with the same name and the same statement;
importing the library brings all of them, with their proofs, into this module. Comparator checks that
each one states exactly what `Challenge.lean` states and uses no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.
-/

@[expose] public section

