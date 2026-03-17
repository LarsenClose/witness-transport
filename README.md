# witness-transport

Core definitions, the positive chain, the carrier architecture, transport theory, encoding invariance, and dynamic drift for the graded reflexive model framework. This is the foundational repository: it defines `GradedReflModel`, proves the forced splitting on Fix(selfApp), the naming extension iff-theorems, the `MinimalNecessityGradient`, the encoding invariance theory (`BoundedGRMEquiv`), the projectional atlas, the `CanonicalMirror` framework, and the dynamic drift generalization. ~69 Lean files, zero sorry.

## Build

```
lake build
```

Requires Lean 4.28.0 and Mathlib.

## Repository graph

```
witness-transport  (core definitions, carrier architecture, transport, invariance)
      |
pnp-integrated     (separation theorem, transport obstruction, anti-compression)
      |
classical-constraints  (seven chains, lock theorems, direct bridges)
      |
classical-bridge   (classical TM model, regime classification, not_P_eq_NP)
```

Each downstream repo mirrors types from upstream repos for import isolation. The canonical `GradedReflModel` is defined here in `WTS/Core.lean`.

## Theorem inventory

See `CLAIMS.md` for the complete theorem inventory with machine-verified axiom profiles.

## Cross-repo notes

The `sideA` theorem (`sideA_bounded_selector_impossible`) is proved here as `selfApp_not_grade_bounded` in `WTS/Shared/SideAMirror.lean`. It is mirrored as an axiom in classical-constraints for import isolation, and proved independently in classical-bridge (4 lines from `SelfAppUnbounded.overflows`). The theorem uses no custom axioms.
