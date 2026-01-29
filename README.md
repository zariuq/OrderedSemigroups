# OrderedSemigroups

Integration of [Eric Paul's OrderedSemigroups library](https://github.com/ericluap/OrderedSemigroups) for use in K&S proofs.

## Why This Matters for Mettapedia

Hölder's theorem (1901) and Alimov's theorem (1950) show that ordered semigroups without "anomalous pairs" embed into (ℝ, +). This provides the shortest proof path for the K&S representation theorem.

Key result used: `holder_not_anom` — NAP implies embeddability into the reals.

## Integration

This directory makes Eric Paul's library consistent with Mettapedia's Lean/Mathlib versions. The library provides:

- `NoAnomalousPairs`: no infinitesimals
- `not_anomalous_pair_commutative`: NAP implies commutativity
- `holder_not_anom`: NAP implies Hölder embedding

## References

- [Project page](https://ericluap.github.io/OrderedSemigroups/)
- [Blueprint](https://ericluap.github.io/OrderedSemigroups/blueprint/)
- Alimov, "On ordered semigroups" (1950)
- Deroin, Navas, Rivas, "Groups, Orders, and Dynamics"
