module

public import MobiusRamsey.Theorem
public import MobiusRamsey.Corollaries

public section

/-!
# Proved solution

`OAI.EuclideanRamsey.Mobius.ramsey_iff_ramsey_mobius_full` (Theorem C) is proved in
`MobiusRamsey/Theorem.lean`; `ramsey_mobius_of_algebraic`, `ramsey_circ_mul_rat` and
`ramsey_circ_add_rat` in `MobiusRamsey/Corollaries.lean`. All of it sits on the module-system port
of OpenAI's EuclideanRamsey development (`OAI/`). `Space`, `Congruent` and `Ramsey` come from
`OAI/Combinatorics/EuclideanRamsey/Model.lean`, and `lorentzForm`, `aug`, `mobiusMap`, `circ` from
`MobiusRamsey/Defs.lean`; Comparator checks that they are identical to the restatements in
`Challenge.lean`.
-/
