# CLAIMS.md — witness-transport

What this project proves, what it assumes, and what it does not claim.

---

## 1. Primary Claim

The project formalizes the collection of language-model pairings as a
mathematical object (the Universal Language Computer), proves that any
single pairing is trivially answerable, characterizes the answer
space — the region between bounded-idempotent selfApp and identity
selfApp where different P vs NP resolutions live — and identifies the
canonical carrier architecture forced by the residual idempotent,
with encoding-invariant obstruction classes and a clean admissible
bridge interface to classical semantics.

**Primary results (ULC refinement tower, fully constructive):**

- `WTS.UniversalLanguageComputer.roundtrip_selfApp_idempotent` — roundtrip forces selfApp idempotence
  - File: `WTS/Tower/UniversalLanguageComputer.lean`
  - Type: `∀ (ulc : UniversalLanguageComputer) (h : ulc.HasRoundtrip), ∀ x, ulc.selfApp (ulc.selfApp x) = ulc.selfApp x`
  - Lean foundational: none | Custom axioms: none
  - Says: any ULC with roundtrip has idempotent selfApp. This is the structural forcing result — no grade, no model, just the two maps.

- `WTS.ULC_conservativity` — both regimes coexist as ULC instances
  - File: `WTS/Tower/ClassicalModels.lean`
  - Type: `(∃ P : UniversalLanguageComputer, P.HasRoundtrip ∧ ∀ x, P.selfApp x = x) ∧ (∃ M : GradedReflModel, M.toULC.HasRoundtrip ∧ SelfAppUnbounded M)`
  - Lean foundational: propext, Quot.sound | Custom axioms: none
  - Says: there exists a ULC with selfApp = id (trivialModel) and a GRM whose ULC embedding has roundtrip with SelfAppUnbounded (standardModel). The second conjunct is stronger than nontrivial selfApp — it witnesses the separation regime. Any single pairing is trivially answerable.

- `WTS.fin_selfApp_eq_id` — pigeonhole forces selfApp = id on finite carriers
  - File: `WTS/Tower/FiniteCarrier.lean`
  - Type: `∀ (n : Nat) (fold unfold : Fin n → Fin n), (∀ x, fold (unfold x) = x) → ∀ x, unfold (fold x) = x`
  - Lean foundational: propext, Quot.sound | Custom axioms: none
  - Says: on finite types, roundtrip forces selfApp = id. Phase transition requires infinite carriers.

- `WTS.three_regime_conservativity` — identity, nontrivial-bounded, unbounded all coexist with roundtrip
  - File: `WTS/Tower/ForcingPredicates.lean`
  - Type: three existentials witnessing (1) selfApp = id with PEqNP, (2) selfApp ≠ id with PEqNP, (3) SelfAppUnbounded
  - Lean foundational: propext, Quot.sound | Custom axioms: none
  - Says: three distinct regimes are each consistent with roundtrip. The gap between bounded-idempotent and identity IS the answer space.

- `WTS.carrier_engineering_trichotomy` — three groups (A/B/C) witnessed by concrete models
  - File: `WTS/Tower/CarrierEngineering.lean`
  - Type: three existentials witnessing compatible-identity, compatible-nontrivial, and incompatible-unbounded retractions
  - Lean foundational: propext, Quot.sound | Custom axioms: none
  - Says: the three-group classification (Group C: selfApp = id; Group B: nontrivial compatible; Group A: incompatible) is witnessed by concrete models.

**Primary results (canonical carrier architecture, core axiom-free; iff-theorems use Lean foundational axioms):**

- `ReflectiveCarrierData` — every GRM induces a canonical section-retraction pair on Fix(selfApp)
  - File: `WTS/Tower/CarrierEngineering/ReflectiveCarrierData.lean`
  - Type: structure with (A, C, incl, norm, sect) where C = Fix(selfApp), unconditional
  - Lean foundational: none | Custom axioms: none
  - Says: the computation layer exists in every GRM without any grade hypothesis or regime assumption. incl . norm = selfApp by construction.

- `SplitIdempotent` equivalence — ReflectiveCarrierData IS the canonical splitting of the idempotent selfApp
  - File: `WTS/Tower/CarrierEngineering/SplitIdempotent.lean`
  - Type: both roundtrips (toSplitIdempotent/toReflectiveCarrierData) hold by `rfl`; Im(e) = Fix(e)
  - Lean foundational: none | Custom axioms: none
  - Says: the carrier architecture is not a construction but an identification. The substrate from Im(selfApp) and the canonical carrier are the same object.

- `carrier_architecture_unique` — any compatible splitting is canonically isomorphic to the fixed-point splitting
  - File: `WTS/Tower/CarrierEngineering/UniversalProperty.lean`
  - Type: factorization theorem with bijection + inclusion + normalization + uniqueness
  - Lean foundational: none | Custom axioms: none
  - Says: the carrier architecture is forced. If your semantics induces an idempotent, there is no design choice.

- `grade_compatible_extension_iff` — strict naming (FixedGradeReflectiveCarrier) exists iff selfApp is grade-non-increasing
  - File: `WTS/Tower/CarrierEngineering/ReflectiveCarrierData.lean`
  - Type: iff statement; unique when inhabited (Subsingleton)
  - Lean foundational: propext, Quot.sound | Custom axioms: none
  - Says: the regime question for a GRM's own grade IS the inhabitation of the strict naming layer.

- `drift_extension_iff` — bounded-loss naming (FixedGradeDriftCarrier) at drift k exists iff selfApp increases grade by at most k
  - File: `WTS/Tower/CarrierEngineering/ReflectiveCarrierData.lean`
  - Type: iff statement; unique when inhabited (Subsingleton); zero drift recovers strict; admissible drifts upward-closed
  - Lean foundational: propext, Quot.sound | Custom axioms: none
  - Says: naming admits a quantitative hierarchy. Every ProtocolGRM admits drift at 2 * transportOverhead.

- `unbounded_gap_iff_no_finite_drift` — UnboundedGap iff no finite drift exists
  - File: `WTS/Tower/CarrierEngineering/ReflectiveCarrierData.lean`
  - Type: iff statement; SelfAppUnbounded and UnboundedGap are independent predicates
  - Lean foundational: propext, Classical.choice, Quot.sound | Custom axioms: none
  - Says: the two obstruction axes (threshold overflow and additive gap) are formally independent. This separation is critical for encoding invariance.

- `leastDrift_stability` — least drift is stable under BoundedGRMEquiv: |k - k'| <= 2c
  - File: `WTS/Tower/CarrierEngineering/LeastDrift.lean`
  - Type: under BoundedGRMEquiv with overhead c, least drifts satisfy |k - k'| <= 2c; zero-overhead preserves exactly
  - Lean foundational: propext, Quot.sound | Custom axioms: none
  - Says: least drift is a robust quantitative invariant, not merely qualitative. THE stability theorem.

- `dynamic_drift_extension_iff` — DynamicDriftCarrier inhabitation iff pointwise selfApp bound
  - File: `WTS/Tower/CarrierEngineering/DynamicDrift.lean`
  - Type: iff between DynamicDriftCarrier inhabitation and pointwise grade bound
  - Lean foundational: propext, Quot.sound | Custom axioms: none
  - Says: the drift function δ(g) generalizes the constant drift k, capturing grade-dependent naming overhead

- `unboundedGap_iff` / `finite_drift_iff` — UnboundedGap and FiniteDrift are invariant under BoundedGRMEquiv
  - File: `WTS/Tower/CarrierEngineering/ReencodingInvariance.lean`
  - Type: biconditional; groupoid structure (refl/symm/trans); NOT invariant: SelfAppUnbounded, strict extension, exact PEqNP threshold
  - Lean foundational: propext, Quot.sound | Custom axioms: none
  - Says: no bounded-overhead reencoding can collapse infinite required drift into finite, or vice versa. The encoding-invariant obstructions.

- `SameSemantics.toBoundedGRMEquiv` — same-semantics encodings induce BoundedGRMEquiv (Bridge theorem)
  - File: `WTS/Tower/CarrierEngineering/AdmissibleBridge.lean`
  - Type: SameSemantics -> BoundedGRMEquiv with overhead = translate_overhead; corollaries: UnboundedGap invariant, FiniteDrift invariant
  - Lean foundational: none | Custom axioms: none
  - Says: the external obligation is reduced to a single interface condition — whether classical encodings satisfy bounded-overhead same-semantics translation.

**Conditional result (assembled content, depends on one cross-project axiom):**

- `WTS.no_bounded_protocol_shortcuts` — conditional on ConsequenceFaithful + ProtocolTransfer, no poly-time SAT solver exists
  - File: `WTS/Protocol/ProtocolWitnessFamilyLock.lean`
  - Type: `(M : GradedReflModel_Mirror) → (hub : SelfAppUnbounded_Mirror M) → (family : SATFamily) → (enc : CookEncoding) → (cf : ConsequenceFaithful enc) → (tr : ProtocolTransfer M family enc cf) → (solver : PolyTimeSolver family) → False`
  - Lean foundational: propext | Custom axioms: **sideA_bounded_selector_impossible_mirror**
  - Says: assuming the protocol encoding is consequence-faithful and transfers to the model, a poly-time SAT solver leads to contradiction. BridgeVacuity (classical-constraints/BridgeVacuity.lean) proves these bridge conditions are moot in TC models: the transfer is uninhabitable when SelfAppUnbounded holds, making this lock regime-characterizing (hypotheses jointly unsatisfiable).

---

## 2. Axiom Profile

All axiom profiles are machine-verified via `lean_verify`.

### Tower content (12 files, no custom axioms)

| Theorem | File | Lean foundational | Custom axioms |
|---|---|---|---|
| `roundtrip_selfApp_idempotent` | `WTS/Tower/UniversalLanguageComputer.lean` | **none** | none |
| `ULC_conservativity` | `WTS/Tower/ClassicalModels.lean` | propext, Quot.sound | none |
| `graded_ulc_conservativity` | `WTS/Tower/GradedULC.lean` | propext, Quot.sound | none |
| `bounded_idempotent_not_forces_identity` | `WTS/Tower/ForcingPredicates.lean` | propext, Quot.sound | none |
| `three_regime_conservativity` | `WTS/Tower/ForcingPredicates.lean` | propext, Quot.sound | none |
| `fin_selfApp_eq_id` | `WTS/Tower/FiniteCarrier.lean` | propext, Quot.sound | none |
| `carrier_engineering_trichotomy` | `WTS/Tower/CarrierEngineering.lean` | propext, Quot.sound | none |
| `projection_forces_PEqNP` | `WTS/Tower/CarrierEngineering/ProjectionObstruction.lean` | **none** | none |
| `projection_contradicts_unbounded` | `WTS/Tower/CarrierEngineering/ProjectionObstruction.lean` | propext, Quot.sound | none |
| `carrier_engineering_dilemma` | `WTS/Tower/CarrierEngineering/ProjectionObstruction.lean` | **none** | none |
| `canonical_mirror_bridge_contradiction` | `WTS/Tower/CarrierEngineering/PartialMirrorAdequacy.lean` | propext, Quot.sound | none |
| `partial_mirror_complete_bridge` | `WTS/Tower/CarrierEngineering/PartialMirrorAdequacy.lean` | **none** | none |
| `universal_chain_instantiation` | `WTS/Tower/CarrierEngineering/ChainInstantiation.lean` | propext, Quot.sound | none |
| `canonicalize_idempotent` (ReflectiveCarrierData) | `WTS/Tower/CarrierEngineering/ReflectiveCarrierData.lean` | **none** | none |
| `grade_compatible_extension_iff` | `WTS/Tower/CarrierEngineering/ReflectiveCarrierData.lean` | propext, Quot.sound | none |
| `drift_extension_iff` | `WTS/Tower/CarrierEngineering/ReflectiveCarrierData.lean` | propext, Quot.sound | none |
| `unbounded_gap_iff_no_finite_drift` | `WTS/Tower/CarrierEngineering/ReflectiveCarrierData.lean` | propext, Classical.choice, Quot.sound | none |
| `splitIdempotent_roundtrip` | `WTS/Tower/CarrierEngineering/SplitIdempotent.lean` | **none** | none |
| `image_eq_fixed` | `WTS/Tower/CarrierEngineering/SplitIdempotent.lean` | **none** | none |
| `carrier_architecture_unique` | `WTS/Tower/CarrierEngineering/UniversalProperty.lean` | **none** | none |
| `factorization` | `WTS/Tower/CarrierEngineering/UniversalProperty.lean` | **none** | none |
| `defectBounded_iff_drift` | `WTS/Tower/CarrierEngineering/DefectSpectrum.lean` | propext, Quot.sound | none |
| `unboundedGap_iff_defect_unbounded` | `WTS/Tower/CarrierEngineering/DefectSpectrum.lean` | **none** | none |
| `exists_least_drift` | `WTS/Tower/CarrierEngineering/LeastDrift.lean` | propext, Classical.choice, Quot.sound | none |
| `leastDrift_stability` | `WTS/Tower/CarrierEngineering/LeastDrift.lean` | propext, Quot.sound | none |
| `dynamic_drift_extension_iff` | `WTS/Tower/CarrierEngineering/DynamicDrift.lean` | propext, Quot.sound | none |
| `actualDriftFn_mono` | `WTS/Tower/CarrierEngineering/DynamicDrift.lean` | propext, Classical.choice, Quot.sound | none |
| `BoundedGRMEquiv.dynamic_drift_transport_mono` | `WTS/Tower/CarrierEngineering/DynamicDrift.lean` | propext, Quot.sound | none |
| `unboundedGap_iff` (invariance) | `WTS/Tower/CarrierEngineering/ReencodingInvariance.lean` | propext, Quot.sound | none |
| `finite_drift_iff` (invariance) | `WTS/Tower/CarrierEngineering/ReencodingInvariance.lean` | propext, Quot.sound | none |
| `drift_transport` | `WTS/Tower/CarrierEngineering/ReencodingInvariance.lean` | propext, Quot.sound | none |
| `SameSemantics.toBoundedGRMEquiv` | `WTS/Tower/CarrierEngineering/AdmissibleBridge.lean` | **none** | none |
| `projectional_no_unboundedGap` | `WTS/Tower/CarrierEngineering/ProjectionalAtlas.lean` | propext, Quot.sound | none |
| `boundary_not_equiv` | `WTS/Tower/CarrierEngineering/ProjectionalAtlas.lean` | propext, Quot.sound | none |
| `projectional_classification` | `WTS/Tower/CarrierEngineering/ProjectionalAtlas.lean` | propext, Quot.sound | none |
| `transport_model_groupC` | `WTS/Tower/FixedPointClassification.lean` | Quot.sound | none |
| `transport_model_ULC` | `WTS/Tower/FixedPointClassification.lean` | Quot.sound | none |

The tower uses standard Lean kernel axioms: `propext` (propositional extensionality) and `Quot.sound` (quotient soundness). `Classical.choice` enters only for biconditionals requiring witness extraction from double negation (`unbounded_gap_iff_no_finite_drift`, `exists_least_drift`) and for `actualDriftFn` / `leastDriftAt` which use `Nat.find` via `Classical.propDecidable`. No custom axioms. No Mathlib.

### Foundation (1 file)

| Theorem | File | Lean foundational | Custom axioms |
|---|---|---|---|
| `conservativity` | `WTS/Core.lean` | propext, Quot.sound | none |

### Assembled content — Transport layer

| Theorem | File | Lean foundational | Custom axioms |
|---|---|---|---|
| `transport_model_selfApp_eq_id` | `WTS/Transport/TransportSelfSimilarity.lean` | Quot.sound | none |
| `sideA_bounded_selector_impossible` | `WTS/Transport/TransportCollapseObstruction.lean` | propext, Quot.sound | none |
| `faithful_zero_overhead_impossible` | `WTS/Transport/TransportCollapseObstruction.lean` | propext, Quot.sound | none |
| `zero_overhead_not_faithful` | `WTS/Transport/TransportCollapseObstruction.lean` | propext, Quot.sound | none |
| `trivialModel_faithful` | `WTS/Transport/TransportCollapseObstruction.lean` | propext | none |

### Assembled content — Shared layer

| Theorem | File | Lean foundational | Custom axioms |
|---|---|---|---|
| `selfApp_nonincreasing_contradiction` | `WTS/Shared/SideAMirror.lean` | propext, Quot.sound | none |

### Assembled content — Protocol layer (uses one custom axiom)

| Theorem | File | Lean foundational | Custom axioms |
|---|---|---|---|
| `no_bounded_protocol_shortcuts` | `WTS/Protocol/ProtocolWitnessFamilyLock.lean` | propext | **`sideA_bounded_selector_impossible_mirror`** |

### The cross-project axiom

There is exactly **one custom axiom** in the assembled content:

```
axiom sideA_bounded_selector_impossible_mirror
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M) (d : Nat) :
    ¬∃ (f : M.carrier → M.carrier),
      (∀ x, M.grade x ≤ d → f x = M.selfApp x) ∧
      (∀ x, M.grade x ≤ d → M.grade (f x) ≤ d)
```

- Declared in: `WTS/Shared/SideAMirror.lean`
- Proved theorem (exact match): `WTS.sideA_bounded_selector_impossible` in `WTS/Transport/TransportCollapseObstruction.lean`
- The axiom mirrors a proved theorem because the two repo layers (constructive/classical) cannot share imports. The architectural decision is documented in BRIDGE_PATH_TABLE.md Section 2.

### Positive chain + substrate (15 files at ReturnPath root)

| File | Lean foundational | Custom axioms |
|---|---|---|
| `WTS/ReturnPath/GrammarFixedPoint.lean` | **none** | none |
| `WTS/ReturnPath/ConstructiveOmega.lean` | **none** | none |
| `WTS/ReturnPath/ReflexiveObject.lean` | Quot.sound | none |
| `WTS/ReturnPath/FixedPointCombinator.lean` | **none** | none |
| `WTS/ReturnPath/Containerization.lean` | **none** | none |
| `WTS/ReturnPath/LambdaModel.lean` | **none** | none |
| `WTS/ReturnPath/IdentityLoop.lean` | **none** | none |
| `WTS/ReturnPath/SelfIndexedComputation.lean` | **none** | none |
| `WTS/ReturnPath/WeakReflData.lean` | **none** | none |
| `WTS/ReturnPath/InvariantSubstrate.lean` | propext, Quot.sound | none |
| `WTS/ReturnPath/SubstrateComputation.lean` | propext, Quot.sound | none |
| `WTS/ReturnPath/StandardModelSubstrate.lean` | propext, Quot.sound | none |
| `WTS/ReturnPath/RedIsSubstrate.lean` | propext, Quot.sound | none |
| `WTS/ReturnPath/PartialReturn.lean` | propext, Quot.sound | none |
| `WTS/ReturnPath/Generator.lean` | propext, Classical.choice, Quot.sound (highest theorem; most theorems at lower levels) | none |

### Generator axiom breakdown (machine-verified)

| Theorem | Lean foundational | Custom axioms |
|---|---|---|
| `tower_complete` | **none** | none |
| `classification_dn` | **none** | none |
| `polymarkov_peqnp` | **none** (PolyMarkov enters as hypothesis) | none |
| `substrate_constructive` | **none** | none |
| `regime_dn` | **none** | none |
| `profile_has_two_degrees_of_freedom` | propext, Quot.sound | none |
| `four_strata` | propext, Quot.sound | none |
| `unbounded_implies_not_peqnp` | propext, Quot.sound | none |
| `classification_classical` | propext, Classical.choice, Quot.sound | none |
| `not_peqnp_implies_unbounded` | propext, Classical.choice, Quot.sound | none |

### Naming dynamics (13 files in ReturnPath/Naming/)

| File | Lean foundational | Custom axioms |
|---|---|---|
| `WTS/ReturnPath/Naming/GradeGapMeasure.lean` | propext, Quot.sound | none |
| `WTS/ReturnPath/Naming/OmegaGradeTransfer.lean` | propext, Quot.sound | none |
| `WTS/ReturnPath/Naming/ReturnPathAtPositions.lean` | propext, Quot.sound | none |
| `WTS/ReturnPath/Naming/CountingBoundary.lean` | propext, Quot.sound | none |
| `WTS/ReturnPath/Naming/DeficitEquivalence.lean` | propext, Classical.choice, Quot.sound | none |
| `WTS/ReturnPath/Naming/SeparationLocalization.lean` | propext, Quot.sound | none |
| `WTS/ReturnPath/Naming/NamingAccess.lean` | propext, Quot.sound | none |
| `WTS/ReturnPath/Naming/ReflexiveToGraded.lean` | propext, Quot.sound | none |

Classical.choice enters only in DeficitEquivalence.lean (via omega on Nat subtraction in Iff goals); all other Naming/ files use propext + Quot.sound only. No custom axioms. No Mathlib. 0 sorry across all 23 active files. GrammarFixedPoint.lean, ConstructiveOmega.lean, and WeakReflData.lean use zero axioms (axiom profile empty). FixedPointCombinator.lean, Containerization.lean, LambdaModel.lean, IdentityLoop.lean, and SelfIndexedComputation.lean are also axiom-free.

5 supplementary files archived to `archive/naming-supplementary/`:
BLLBridge.lean, BLLTowerLevels.lean, ContainerRestriction.lean,
GradedSubObjects.lean, Level4PneNP.lean. All 0 sorry, propext + Quot.sound
only. Archived because their content elaborates interpretive frameworks
(BLL, container restriction, graded sub-objects) that are not on the
critical path of the main argument.

### sorry count

Zero. Verified by grep across all `.lean` files excluding `.lake/`.

---

## 3. What Is Proved (Unconditional)

Every theorem listed below holds without open hypotheses. Organized by directory. Theorems marked **[critical path]** are on the main argument's dependency chain; others are **[supplementary]**.

### Foundation (1 file, assembled from pnp-integrated)

**WTS/Core.lean** — Central definitions and concrete models.

Structures and definitions:
- `GradedReflModel` — the central structure: carrier, fold, unfold, roundtrip, grade
- `selfApp` — `unfold ∘ fold`, the function whose boundedness determines the regime
- `FactorsThrough` — `f` preserves grade bound `d`
- `SelfAppUnbounded` — selfApp overflows every grade level
- `TuringComplete` — unbounded elements + selfApp unbounded
- `PEqNP` — selfApp factors through some grade level
- `trivialModel` — Unit carrier, id fold/unfold, grade 0. P = NP here. **[critical path]**
- `standardModel` — Nat carrier, fold = ÷2, unfold = 2x+1. P ≠ NP here. **[critical path]**
- `CompModel` / `CompModelPoly` — abstract step-bounded computation model
- `BinaryModel` / `LinearBinaryModel` / `GradeStructure` — binary counting structures
- `N_Val` / `N_End` — binary value and endomorphism counting functions

Key theorems:
- `verification_factors` — verification (fold ∘ unfold) factors through every grade. **[critical path]**
- `selfApp_not_factors` — selfApp does not factor through any grade when unbounded. **[critical path]**
- `verification_ne_solving` — verification ≠ solving when selfApp is unbounded. **[critical path]**
- `from_turing_complete` — Turing completeness implies separation. **[critical path]**
- `conservativity` — both regimes exist: `trivialModel` witnesses selfApp = id, `standardModel` witnesses SelfAppUnbounded. **[critical path]**
- `trivial_selfApp_eq_id` — trivialModel has selfApp = id. **[critical path]**

Supplementary (13 utility lemmas): `gt_le_absurd`, `two_pow_succ_gt`, `two_pow_strict_mono`, `two_pow_mono`, `two_pow_ge_2`, `pow_self_ge_two_pow`, `two_pow_gt_n`, `two_pow_ge_succ`, `pow_self_ge_sq`, `two_pow_ge_sq`, `N_Val_pos`, `N_Val_ge_2`, `N_Val_mono`, `N_Val_mono_succ`, `overflowGrade_even`, `overflowGrade_odd`, `standardModel_overflow`.

### ULC Refinement Tower (7 files, fully constructive)

**WTS/Tower/UniversalLanguageComputer.lean** — The ULC definition and idempotence.

- `UniversalLanguageComputer` — structure: two types (Lang, CompModel), two maps (encode, decode), no axioms. **[critical path]**
- `selfApp` / `HasRoundtrip` — selfApp definition and roundtrip predicate. **[critical path]**
- `roundtrip_selfApp_idempotent` — roundtrip forces selfApp idempotence. THE structural forcing result. **[critical path]**
- `unified_hasRoundtrip_and_selfApp_eq_id` — the unified pairing (one type, id maps) has roundtrip and selfApp = id. **[supplementary]**
- `exists_non_idempotent` — a ULC without roundtrip can have non-idempotent selfApp. **[supplementary]**

**WTS/Tower/ClassicalModels.lean** — GRM embeds as ULC.

- `GradedReflModel.toULC` — every GRM yields a ULC. **[critical path]**
- `toULC_hasRoundtrip` — the embedding preserves roundtrip. **[critical path]**
- `toULC_selfApp_eq` — selfApp agrees under embedding. **[critical path]**
- `toULC_idempotent` — idempotence transfers. **[supplementary]**
- `trivialModel_ULC_selfApp_id` — trivialModel's ULC has selfApp = id. **[critical path]**
- `standardModel_ULC_selfApp_unbounded` — standardModel's ULC has nontrivial selfApp. **[critical path]**
- `phase_structure` — regimes separate at ULC level. **[supplementary]**
- `ULC_conservativity` — both regimes coexist as ULC instances. **[critical path]**

**WTS/Tower/GradedULC.lean** — Graded ULC predicates.

- `ULCGrade` — grade structure on ULC. **[critical path]**
- `ULCSelfAppBounded` / `ULCSelfAppUnbounded` — regime predicates at ULC level. **[critical path]**
- `GradedReflModel.toULCGrade` — GRM yields graded ULC. **[critical path]**
- `grm_bounded_iff` / `grm_unbounded_iff` — GRM regime predicates match ULC regime predicates. **[critical path]**
- `ulc_regime_contradiction` — bounded and unbounded are mutually exclusive. **[critical path]**
- `graded_ulc_conservativity` — both graded regimes coexist. **[critical path]**

**WTS/Tower/ForcingPredicates.lean** — The forcing gap.

- `retractionModel` — Nat carrier, fold = ÷2, unfold = 2×. Bounded-idempotent, not identity. **[critical path]**
- `retractionModel_selfApp_idempotent` — selfApp is idempotent. **[critical path]**
- `retractionModel_selfApp_grade_le` — selfApp is grade-non-increasing. **[critical path]**
- `retractionModel_selfApp_bounded` — selfApp factors through every grade. **[supplementary]**
- `retractionModel_PEqNP` — PEqNP holds. **[supplementary]**
- `retractionModel_selfApp_ne_id` — selfApp(1) = 0 ≠ 1. **[critical path]**
- `bounded_idempotent_not_forces_identity` — THE GAP THEOREM. There exists a model where selfApp is idempotent and bounded but ≠ id. **[critical path]**
- `three_regime_conservativity` — identity, nontrivial-bounded, unbounded all coexist. **[critical path]**
- `grm_roundtrip_forces_idempotent` — roundtrip forces idempotence at GRM level. **[critical path]**
- `regime_not_forced_by_roundtrip` — both PEqNP and ¬PEqNP are consistent with roundtrip. **[supplementary]**

**WTS/Tower/FiniteCarrier.lean** — Finite-carrier theorem.

- `fin_injective_le` — pigeonhole: injection Fin n → Fin m implies n ≤ m. **[critical path]**
- `fin_injective_surjective` — injective endofunction on Fin n is surjective. **[critical path]**
- `fin_left_inverse_right_inverse` — left inverse is right inverse on Fin n. **[critical path]**
- `fin_selfApp_eq_id` — THE FINITE-CARRIER THEOREM. On Fin n, roundtrip forces selfApp = id. **[critical path]**
- `finite_grm_selfApp_eq_id` — GRM corollary: any GRM with carrier Fin n has selfApp = id. **[supplementary]**
- `finite_carrier_no_separation` — SelfAppUnbounded is impossible on Fin n. **[critical path]**
- `finite_carrier_zero_gap` — gradeGap = 0 on all finite carriers. **[critical path]**
- `finite_carrier_groupC` — finite carriers force Group C: selfApp = id ∧ gradeGap = 0 ∧ PEqNP. **[critical path]**
- `nontrivial_selfApp_requires_infinite_carrier` — nontrivial selfApp requires infinite carrier, witnessed by standardModel. **[critical path]**

**WTS/Tower/CarrierEngineering.lean** — Three-group classification.

- `GradedRetraction` — idempotent retraction with grade. **[critical path]**
- `GradedRetraction.Compatible` — grade-non-increasing. **[critical path]**
- `compatible_factors` — compatible implies FactorsThrough every grade level. **[supplementary]**
- `groupC` — identity retraction. **[critical path]**
- `groupC_always_compatible` — identity is always compatible. **[critical path]**
- `GroupBData` — retraction with grade-non-increasing witness. **[critical path]**
- `groupB_compatible` — Group B is compatible by construction. **[critical path]**
- `GradedReflModel.toGradedRetraction` — every GRM yields a GradedRetraction via selfApp. **[critical path]**
- `compatible_retraction_gives_PEqNP` — compatible retraction implies PEqNP. **[critical path]**
- `incompatible_retraction_gives_separation` — incompatible (unbounded) implies ¬PEqNP. **[critical path]**
- `carrier_engineering_trichotomy` — THE TRICHOTOMY. Three groups witnessed by concrete models. **[critical path]**

**WTS/Tower/CarrierEngineering/ProjectionObstruction.lean** — Projection obstruction: nontrivial idempotent grade-non-increasing canonicalizers cannot be realized as full-carrier selfApp.

- `IdempotentNormalizer` — structure: idempotent grade-non-increasing normalizer on a graded type. **[critical path]**
- `projection_forces_PEqNP` — grade-non-increasing selfApp forces PEqNP. Axioms: **none**. **[critical path]**
- `projection_contradicts_unbounded` — grade-non-increasing selfApp + SelfAppUnbounded = False. **[critical path]**
- `normalizer_forces_PEqNP` — specialization to IdempotentNormalizer. **[critical path]**
- `normalizer_contradicts_unbounded` — normalizer + SelfAppUnbounded = False. **[critical path]**
- `restriction_collapses_to_identity` — on Fix(normalize), normalize = id. **[critical path]**
- `carrier_engineering_dilemma` — full carrier => PEqNP; restricted carrier => selfApp = id (Group C). Axioms: **none**. **[critical path]**
- `retractionModel_witnesses_obstruction` — retractionModel concretely witnesses the obstruction. **[supplementary]**
- `standardModel_no_normalizer` — standardModel has no grade-non-increasing selfApp. **[supplementary]**

**WTS/Tower/CarrierEngineering/CanonicalMirror.lean** — Canonical mirror structure for Group B carrier engineering.

- `CanonicalMirror` — structure: section-retraction pair between ambient carrier A and canonical subdomain C. **[critical path]**
- `CanonicalMirror.canonicalize_idempotent` — induced endomorphism is idempotent. **[critical path]**
- `CanonicalMirror.canonicalize_grade_le` — induced endomorphism is grade-non-increasing. **[critical path]**
- `CanonicalMirror.incl_injective` — inclusion is injective. **[critical path]**
- `CanonicalMirror.canonical_iff_in_image` — fixed points = image of incl. **[critical path]**
- `CanonicalMirror.toNormalizer` — yields IdempotentNormalizer on ambient carrier. **[critical path]**
- `CanonicalMirror.toGroupBData` — yields GroupBData on ambient carrier. **[critical path]**
- `CanonicalMirror.ofIdempotentEndo` — construct from idempotent endomorphism (canonical construction). **[critical path]**
- `CanonicalMirror.ofIdempotentEndo_canonicalize` — canonicalizer IS the original red. **[critical path]**

**WTS/Tower/CarrierEngineering/PartialMirrorAdequacy.lean** — Bridge arguments go through on CanonicalMirror without a full GRM.

- `partial_mirror_selfApp_bounded` — canonicalize is grade-bounded at every grade. **[critical path]**
- `partial_mirror_factors_through` — canonicalize factors through every grade level. **[critical path]**
- `canonical_mirror_bridge_contradiction` — overflow + CanonicalMirror = False. **[critical path]**
- `canonical_mirror_transfer_contradiction` — variant with transfer function. **[critical path]**
- `CanonicalMirrorWithSelfApp.contradicts_unbounded` — selfApp = canonicalize + unbounded = False. **[critical path]**
- `partial_mirror_complete_bridge` — 5-property conjunction: idempotent, grade-non-increasing, identity on subdomain, FactorsThrough, GroupBData. Axioms: **none**. **[critical path]**
- `canonicalMirror_of_modelData` — entry point for chain instantiation from ModelData fields. **[critical path]**
- `modelData_bridge` — FactorsThrough + idempotent + no overflow for any ModelData. **[critical path]**

**WTS/Tower/CarrierEngineering/ChainInstantiation.lean** — Group B chain instantiations of the CanonicalMirror interface.

- `universal_chain_instantiation` — any idempotent grade-non-increasing red yields full bridge package. **[critical path]**
- `chain5_bridge_properties` — Chain 5 pattern (multilinear reduction) bridge. **[supplementary]**
- `chain2_bridge_properties` — Chain 2 pattern (protocol flattening) bridge. **[supplementary]**
- `chain3_bridge_properties` — Chain 3 pattern (NNF conversion) bridge. **[supplementary]**
- `three_chains_one_pattern` — all three Group B chains instantiate the same CanonicalMirror pattern. **[supplementary]**

**WTS/Tower/CarrierEngineering/ProjectionalAtlas.lean** — Projectional semantics atlas: every natural canonicalization regime across all seven chains is projectional, with invariant boundary against standardModel.

- `projectional_no_unboundedGap` — grade-non-increasing selfApp implies ¬UnboundedGap. **[critical path]**
- `ProjectionalPattern` — structure: named idempotent grade-non-increasing Nat endomorphism. **[critical path]**
- `atlas_chain1` — Group A / Chain 1 (SAT): Boolean evaluation, cap at 1. **[supplementary]**
- `atlas_chain4` / `atlas_chain4_projectional` — Group A / Chain 4 (CSP): domain-K evaluation, cap at K; proved for every K. **[supplementary]**
- `atlas_chain6` — Group A / Chain 6 (extension complexity): nonneg rank, identity. **[supplementary]**
- `atlas_chain5` / `atlas_chain2` / `atlas_chain3` — Group B chain patterns (multilinear reduction, protocol flatten, NNF conversion). **[supplementary]**
- `atlas_identity` — Group C / Chain 7: identity pattern. **[supplementary]**
- `atlas_evalK` — parametric evaluation-K family: projectional for every K. **[supplementary]**
- `atlas_constant` — constant projection pattern. **[supplementary]**
- `fixed_chains_projectional` — chains 1, 2, 3, 5, 6, and identity each satisfy idempotent conjunction; chain 4 proved separately parameterized by K. **[supplementary]**
- `boundary_witness` — standardModel witnesses UnboundedGap. **[critical path]**
- `boundary_not_equiv` — standardModel cannot be BoundedGRMEquiv to any projectional GRM. **[critical path]**
- `projectional_classification` — Full classification: (1) grade-non-increasing selfApp → PEqNP, (2) standardModel witnesses UnboundedGap, (3) boundary invariant under BoundedGRMEquiv. **[critical path]**

Coverage: Group A (chains 1, 4, 6) via evaluation-bounded semantics (Boolean cap / domain-K cap / rank identity); Group B (chains 2, 3, 5) via explicit idempotent canonicalizers; Group C (chain 7) via identity. All seven chains' natural semantics are projectional.

Lean foundational: propext, Quot.sound (inherited from ReencodingInvariance imports) | Custom axioms: none. 9 atlas entries covering all 7 chains, 0 sorry.

**WTS/Tower/CarrierEngineering/ReflectiveCarrierData.lean** — Master carrier structure: three-layer design.

Structures:
- `ReflectiveCarrierData` — ungraded section-retraction pair (A, C, incl, norm, sect). Every GRM instantiates via C = Fix(selfApp). **[critical path]**
- `FixedGradeReflectiveCarrier` — strict naming layer: grade-compatible extension. **[critical path]**
- `FixedGradeDriftCarrier` — bounded-loss naming layer with drift parameter k. **[critical path]**
- `AdmitsDrift` / `FiniteDrift` / `UnboundedGap` — three predicates on the naming obstruction. **[critical path]**

Key theorems:
- `canonicalize_idempotent` — incl . norm is idempotent. **[critical path]**
- `canonicalize_incl` — incl(norm(x)) = selfApp(x). **[critical path]**
- `incl_injective` — norm is a left inverse. **[critical path]**
- `grade_compatible_extension_iff` — strict naming iff selfApp grade-non-increasing. **[critical path]**
- `instSubsingleton` (FixedGradeReflectiveCarrier) — strict naming unique when inhabited. **[critical path]**
- `drift_extension_iff` — drift k naming iff grade increase bounded by k. **[critical path]**
- `instSubsingleton` (FixedGradeDriftCarrier) — drift naming unique at each k. **[critical path]**
- `admitsDrift_mono` — admissible drifts upward-closed. **[critical path]**
- `unbounded_gap_iff_no_finite_drift` — UnboundedGap iff no finite drift. **[critical path]**
- `disruption_iff_non_cotrip` — SelfAppUnbounded iff not cotrip closure. **[critical path]**

Three axiom tiers: (1) ungraded carrier structure is axiom-free; (2) graded extension iff statements (grade_compatible_extension_iff, drift_extension_iff, admitsDrift_mono, standardModel_unboundedGap) use propext + Quot.sound; (3) biconditionals connecting existential and negated forms (finiteDrift_iff_not_unboundedGap, unbounded_gap_iff_no_finite_drift, selfAppUnbounded_iff_not_PEqNP, no_strict_extension_of_unbounded_gap, disruption_iff_non_cotrip, asymmetric_projection_iff_non_cotrip) add Classical.choice for the direction that extracts witnesses from double negation.

**WTS/Tower/CarrierEngineering/SplitIdempotent.lean** — ReflectiveCarrierData IS the canonical splitting of an idempotent.

- `SplitIdempotent` — structure: idempotent e with carrier C, incl, norm, with incl . norm = e and norm . incl = id. **[critical path]**
- `toSplitIdempotent` — ReflectiveCarrierData → SplitIdempotent. **[critical path]**
- `toReflectiveCarrierData` — SplitIdempotent → ReflectiveCarrierData via Fix(e). **[critical path]**
- `splitIdempotent_roundtrip` / `reflectiveCarrierData_roundtrip` — both roundtrips by `rfl`. **[critical path]**
- `image_eq_fixed` — Im(e) = Fix(e). **[critical path]**
- `GradedSplitIdempotent` / `DriftedSplitIdempotent` — graded and drifted variants. **[critical path]**

All axiom-free. 20 theorems total.

**WTS/Tower/CarrierEngineering/UniversalProperty.lean** — The splitting is unique up to unique isomorphism.

- `CompatibleSplitting` — any (C', incl', norm') with incl' . norm' = e. **[critical path]**
- `toFixed` / `fromFixed` — comparison maps between compatible splitting and Fix(e). **[critical path]**
- `toFixed_fromFixed` / `fromFixed_toFixed` — mutually inverse. **[critical path]**
- `toFixed_unique` / `fromFixed_unique` — uniqueness of comparison maps. **[critical path]**
- `norm_intertwines` — toFixed . norm' = canonical norm. **[critical path]**
- `factorization` — bijection + inclusion + normalization + uniqueness, bundled. **[critical path]**
- `compare` / `compare_inverse` / `compare_preserves_incl` — any two compatible splittings canonically isomorphic. **[critical path]**
- `carrier_architecture_unique` — for AdmissibleEncodings: if semantics induces idempotent, carrier architecture is forced. **[critical path]**

All axiom-free. 25 theorems total.

**WTS/Tower/CarrierEngineering/DefectSpectrum.lean** — Defect as pointwise naming loss.

- `gap` — grade(selfApp(x)) - grade(x): pointwise defect. **[critical path]**
- `DefectBoundedAt` / `DefectBounded` — local and global defect bounds. **[critical path]**
- `DefectExceeds` — defect exceeds threshold at grade d. **[critical path]**
- `defectBounded_iff_drift` — DefectBounded k iff AdmitsDrift k. **[critical path]**
- `defectBounded_zero_iff_strict` — DefectBounded 0 iff strict naming. **[critical path]**
- `finiteDrift_iff_defect_bounded` — FiniteDrift iff exists k with DefectBounded k. **[critical path]**
- `unboundedGap_iff_defect_unbounded` — UnboundedGap iff defect exceeds every bound. **[critical path]**
- `defectBounded_transport` — defect shifts by at most 2c under BoundedGRMEquiv. **[critical path]**
- `DefectEquivalent` — coarse defect class with refl/symm/trans. **[critical path]**

Core definitions and forward implications axiom-free; `defectBounded_iff_drift` uses propext, Quot.sound. 35 theorems total.

**WTS/Tower/CarrierEngineering/LeastDrift.lean** — The minimum admissible drift.

- `IsLeastDrift` — predicate: k is least drift (admits k, no j < k). **[critical path]**
- `exists_least_drift` — FiniteDrift implies exists least drift (well-ordering of Nat). **[critical path]**
- `isLeastDrift_unique` — least drift is unique. **[critical path]**
- `minDrift` — noncomputable extraction via Nat.find. **[critical path]**
- `leastDrift_stability` — THE STABILITY THEOREM: |k - k'| <= 2c under BoundedGRMEquiv with overhead c. **[critical path]**
- `leastDrift_eq_of_zero_overhead` — zero-overhead preserves exactly. **[critical path]**
- `leastDrift_stability_chain` — stability through trans composition. **[critical path]**
- `isLeastDrift_zero_iff` — IsLeastDrift 0 iff strict naming. **[critical path]**
- `exists_leastDrift_bounded` — ProtocolGRM least drift <= 2 * transportOverhead. **[critical path]**

`exists_least_drift` uses propext, Classical.choice, Quot.sound (well-ordering extraction); `leastDrift_stability` uses propext, Quot.sound; `minDrift` extraction uses Classical.choice. Predicate definitions axiom-free. 27 theorems total.

**WTS/Tower/CarrierEngineering/DynamicDrift.lean** — Generalization from constant drift to grade-dependent drift functions.

The constant drift formulation (FixedGradeDriftCarrier) captures "selfApp increases grade by at most k everywhere." The actual structural object is the drift function δ(g) = sup{ grade(selfApp(x)) − grade(x) | grade(x) ≤ g }, which is grade-dependent.

Structures:
- `DynamicDriftCarrier` — naming layer with drift : Nat → Nat, bounding grade_C(norm a) ≤ grade_A(a) + drift(grade_A(a)). Subsingleton: grade_compat forces grade_C uniquely. **[critical path]**
- `GradedReflModel.DynamicDriftCompatibleExtension` — abbreviation tying DynamicDriftCarrier to a GRM. **[critical path]**

Special-case coercions:
- `FixedGradeDriftCarrier.toDynamic` — every constant-drift carrier yields a DynamicDriftCarrier. **[critical path]**
- `DynamicDriftCarrier.toFixed` / `toStrict` — constant drift and zero drift recover FixedGradeDriftCarrier / FixedGradeReflectiveCarrier. **[critical path]**

Inhabitation and monotonicity:
- `dynamic_drift_extension_iff` — GRM admits a dynamic drift extension with δ iff selfApp satisfies grade(selfApp(x)) ≤ grade(x) + δ(grade(x)) pointwise. Special cases: δ = const k recovers drift_extension_iff; δ = 0 recovers strict; δ eventually-zero captures classicalGRM. **[critical path]**
- `dynamic_drift_mono` — pointwise-smaller drift function admits extension if larger does. **[critical path]**
- `dynamic_drift_const_iff` — constant-function specialization recovers DriftCompatibleExtension. **[critical path]**

Grade-localized drift bounds and actual drift function:
- `HasBoundedDriftAt` / `leastDriftAt` — grade-localized versions of FiniteDrift / minDrift. `leastDriftAt` uses Nat.find + Classical.propDecidable. **[critical path]**
- `actualDriftFn` — the pointwise-least admissible drift function (noncomputable, uses Classical.choice via Nat.find). **[critical path]**
- `actualDriftFn_bound` / `actualDriftFn_minimal` — correctness and minimality of actualDriftFn. **[critical path]**
- `admits_actualDriftFn` — every FiniteDrift GRM admits its actual drift function as a DynamicDriftCompatibleExtension. **[critical path]**
- `actualDriftFn_mono` — actualDriftFn is non-decreasing: higher grades allow at least as much drift. **[critical path]**
- `actualDriftFn_le_minDrift` — actualDriftFn is bounded above by the global minDrift. **[critical path]**
- `actualDriftFn_zero_of_isLeastDrift_zero` — under IsLeastDrift 0 (Group B/C), actualDriftFn is zero everywhere. **[critical path]**
- `actualDriftFn_ge_minDrift_at_witness` — at grades that realize the global minimum, actualDriftFn = minDrift. **[supplementary]**

Encoding invariance:
- `BoundedGRMEquiv.dynamic_drift_transport_mono` — non-decreasing drift δ in M yields drift fun g => δ(g + overhead) + 2*overhead in M', under BoundedGRMEquiv. **[critical path]**
- `BoundedGRMEquiv.dynamic_drift_transport_mono_g` — reverse direction. **[critical path]**
- `BoundedGRMEquiv.const_drift_from_dynamic_transport` — constant drift recovers drift_transport as a special case. **[critical path]**

Drift function classes:
- `EventuallyZeroDrift` / `EventuallyZeroDriftBounded` — drift is zero above a threshold (captures classicalGRM-style models). **[critical path]**
- `eventuallyZeroDriftBounded_finiteDrift` — EventuallyZeroDriftBounded implies FiniteDrift. **[critical path]**
- `eventuallyZeroDriftBounded_dynamic` — yields a better (non-constant) dynamic drift witness than the constant-k bound. **[critical path]**
- `LinearDriftBounded` — grade(selfApp(x)) ≤ grade(x) * (a+1) + b. Zero slope recovers FiniteDrift; positive slope gives dynamic but not finite drift. **[supplementary]**
- `posSlope_dynamic_drift` — positive-slope linear drift gives DynamicDriftCompatibleExtension. **[supplementary]**
- `HasSublinearDrift` — structural definition for the gap between FiniteDrift and UnboundedGap. **[supplementary]**

Connection to FiniteDrift:
- `finiteDrift_iff_actualDriftFn_bounded` — FiniteDrift ↔ actualDriftFn is uniformly bounded. **[critical path]**

Axiom profile: `DynamicDriftCarrier` definition and forward implications axiom-free; iff-theorems and drift transport use propext, Quot.sound; `leastDriftAt` / `actualDriftFn` / `actualDriftFn_mono` / `actualDriftFn_minimal` use Classical.choice (via Nat.find + Classical.propDecidable). No custom axioms. 0 sorry. ~35 theorems total.

**WTS/Tower/CarrierEngineering/ReencodingInvariance.lean** — Encoding-invariant obstruction classes.

- `BoundedGRMEquiv` — carrier bijection with bounded additive grade distortion and selfApp compatibility. **[critical path]**
- `gap_distortion` — core lemma: gap at x exceeds k+2c in M implies gap at f(x) exceeds k in M'. **[critical path]**
- `drift_transport` / `drift_extension_transport` — drift k in M gives drift k+2c in M'. **[critical path]**
- `unboundedGap_iff` — UnboundedGap invariant (biconditional). **[critical path]**
- `finite_drift_iff` — FiniteDrift invariant (biconditional). **[critical path]**
- `fFixed` / `gFixed` — bijection between Fix(selfApp_M) and Fix(selfApp_M'). **[critical path]**
- `refl` / `symm` / `trans` — groupoid structure (overhead 0, same, c1+c2). **[critical path]**

NOT invariant (proved): SelfAppUnbounded (threshold absorbed by overhead), strict extension (drift 0 becomes 2c), exact PEqNP threshold.

Forward directions and groupoid structure axiom-free; biconditionals (`unboundedGap_iff`, `finite_drift_iff`) and `drift_transport` use propext, Quot.sound; Classical.choice isolated to reverse directions of equivalences. 30 theorems total.

**WTS/Tower/CarrierEngineering/AdmissibleBridge.lean** — Interface to classical computation.

- `AdmissibleEncoding` — carrier Names, fold/unfold, roundtrip, grade, overhead, selfApp_bounded. **[critical path]**
- `AdmissibleEncoding.toGRM` — induces a GRM. **[critical path]**
- `AdmissibleEncoding.admits_drift` — admits drift at its overhead. **[critical path]**
- `SameSemantics` — two encodings with bounded translations commuting with selfApp; refl/symm/trans. **[critical path]**
- `SameSemantics.toBoundedGRMEquiv` — Bridge theorem: same-semantics induces BoundedGRMEquiv with overhead = translate_overhead. **[critical path]**
- `SameSemantics.unboundedGap_iff` / `finiteDrift_iff` — invariants transfer across same-semantics. **[critical path]**

All axiom-free. 17 theorems total.

**WTS/Tower/CarrierEngineering/MinimalNecessityGradient.lean** — Packaging: recoverable theorem complex.

- Bundles the full carrier architecture into a single recoverable statement:
  1. fold/unfold forces idempotent selfApp
  2. idempotent determines canonical kernel on Fix(selfApp)
  3. any compatible carrier factors uniquely through it
  4. strict naming exactly when grade-non-increasing
  5. bounded-loss naming exactly when bounded by +k
  6. least drift is minimum naming loss
  7. qualitative defect class is invariant under bounded reencoding
- Re-exports from LeastDrift and UniversalProperty.

All axiom-free. **[critical path]**

**WTS/Tower/FixedPointClassification.lean** — Transport model satisfies Group C predicates.

- `transport_model_compatible` — transport model retraction is compatible. **[critical path]**
- `transport_model_groupC` — transport model satisfies all Group C predicates: Compatible, selfApp = id, PEqNP. **[critical path]**
- `transport_model_ULC` — transport model as ULC instance has roundtrip + selfApp = id. **[critical path]**

### Return Path — Root (15 files: positive chain + substrate + generator)

The positive chain (8 files, axiom empty) and substrate results carry the
paper's Sections 1-3 content. Generator.lean carries Section 4b.

**WTS/ReturnPath/GrammarFixedPoint.lean** — Grammar-level fixed point.

- `GCat` — the categorical grammar: 2 sorts, 1 composition, 1 identity, 2 laws. **[critical path]**
- `M_GCat_is_GCat` — M(G_Cat) = G_Cat: the grammar reproduces itself. Axioms: **none**. **[critical path]**

**WTS/ReturnPath/ConstructiveOmega.lean** — Y combinator at axiom level empty.

- `omega_fixed_point` — categorical Y combinator fixed-point equation. Axioms: **none**. **[critical path]**
- `ReflData` — reflexive data: isomorphism [A, L] = L. **[critical path]**

**WTS/ReturnPath/ReflexiveObject.lean** — D = (D -> D) at type level.

- `selfApp_fold` — selfApp = unfold . fold. **[critical path]**
- `unfold_fold_id` — roundtrip: fold . unfold = id. **[critical path]**

**WTS/ReturnPath/FixedPointCombinator.lean** — Y combinator from reflexive object.

- `Y_fixed_point` — Y(f) = f(Y(f)). **[critical path]**

**WTS/ReturnPath/Containerization.lean** — Closed container from reflexive object.

- `eval_selfReference` — quine self-recognition. **[critical path]**
- `comp_assoc` / `idElem_comp` / `comp_idElem` — composition associativity and units. **[critical path]**

**WTS/ReturnPath/LambdaModel.lean** — Lambda model from ReflData.

- `reflData_beta` — beta law holds. **[critical path]**
- `reflData_eta` — eta law holds (requires full iso). **[critical path]**
- `lambda_model_fixed_point` — every endomorphism has a fixed point. **[critical path]**

**WTS/ReturnPath/IdentityLoop.lean** — Quine self-recognition.

- `quine_self_recognition` — evaluating the quine recovers selfApp. **[critical path]**

**WTS/ReturnPath/SelfIndexedComputation.lean** — Self-indexed naming and Kleene.

- `selfApp_recovers_named` — the evaluator recovers named operations. **[critical path]**
- `self_indexed_kleene` — self-indexed Kleene fixed-point theorem. **[critical path]**
- `naming_roundtrip_recover` — naming recovery (requires full iso). **[critical path]**

**WTS/ReturnPath/WeakReflData.lean** — Computation/naming boundary.

- `weak_omega_fixed_point` — Y combinator survives with retraction only. Axioms: **none**. **[critical path]**
- `weakBeta` — beta law survives with retraction only. Axioms: **none**. **[critical path]**
- Eta does NOT survive — requires full isomorphism. This is the boundary. **[critical path]**

**WTS/ReturnPath/InvariantSubstrate.lean** — Im(selfApp) in every GRM.

- `InvariantSubstrate.ofSelfApp` — construct substrate from any element via selfApp. **[critical path]**
- `substrate_zero_gap` — gradeGap = 0 on Im(selfApp). **[critical path]**
- `substrate_PEqNP` — P = NP on Im(selfApp). **[critical path]**
- `substrate_computation_free` — selfApp contributes zero overhead on its image. **[critical path]**

**WTS/ReturnPath/SubstrateComputation.lean** — Six-property conjunction.

- `substrate_universal_computation` — full iso + selfApp = id + gradeGap = 0 + beta + omega = f + omega output returns to substrate. **[critical path]**
- `separation_regime_has_substrate` — even standardModel has this substrate on Im(selfApp). **[critical path]**

**WTS/ReturnPath/StandardModelSubstrate.lean** — Concrete substrate.

- `standardModel_image_iff_odd` — Im(selfApp) = odd naturals. **[critical path]**
- `standardModel_naming_gap` — even naturals are the naming gap. **[critical path]**

**WTS/ReturnPath/RedIsSubstrate.lean** — Chain-specific red as substrate.

- `red_idempotent` — derivable from selfApp_eq_red + idempotence. **[critical path]**
- `red_image_is_substrate` — Im(red) = Im(selfApp) = invariant substrate. **[critical path]**

### Return Path — Naming dynamics (13 files in `WTS/ReturnPath/Naming/`)

Quantitative characterization of the answer space interior and the
naming layer's relationship to the invariant substrate.

**WTS/ReturnPath/Naming/GradeGapMeasure.lean** — gradeGap as quantitative ruler.

- `gradeGap` — `(grade(selfApp(x)) : Int) - (grade(x) : Int)`, distance from identity. **[critical path]**
- `compatible_iff_nonpositive_gap` — Compatible iff gradeGap <= 0 everywhere. Bridge between CarrierEngineering predicates and grade dynamics. **[critical path]**
- `gap_trichotomy` — three regimes (zero/nonpositive/unbounded) witnessed by concrete models. **[critical path]**
- `selfApp_image_zero_gap` — image of selfApp always has zero gap (idempotent projection). **[critical path]**
- `nonpositive_gap_implies_PEqNP` — nonpositive gap implies PEqNP via Compatible. **[supplementary]**

**WTS/ReturnPath/Naming/OmegaGradeTransfer.lean** — omega grade overhead = gradeGap.

- `compatible_composition_grade` — Compatible + f has overhead c implies grade(f(selfApp(x))) <= grade(x) + c. **[critical path]**
- `compatible_composition_factors` — Compatible + f factors through d implies f . selfApp factors through d. Non-vacuous injection bound in FactorsThrough language. **[critical path]**
- `gradeGap_determines_factoring` — gradeGap ≤ 0 → selfApp factors through every grade; SelfAppUnbounded → factors through none. Non-vacuous replacement for omega_grade_transfer. **[critical path]**
- `gradeGap_determines_regime` — nonpositive gradeGap → PEqNP, unbounded → ¬PEqNP, both regimes concretely witnessed. **[critical path]**
- `grade_transfer_trichotomy` — both regimes witnessed for composition. **[supplementary]**
- `composition_at_retracted_point` — on image of selfApp, overhead is exactly c_f (universal, all regimes). **[supplementary]**

**WTS/ReturnPath/Naming/ReturnPathAtPositions.lean** — transport model grade at different positions.

- `transport_model_zero_gap` — T(M) has gradeGap = 0 for ANY M (universal). **[critical path]**
- `universal_grade_contrast` — base has unbounded gap, transport has zero gap. **[critical path]**
- `return_path_at_all_positions` — three concrete positions characterized. **[supplementary]**

**WTS/ReturnPath/Naming/CountingBoundary.lean** — growth gap at resource bounds.

- `binary_has_growth_gap` — HasGrowthGap N_End N_Val c for every overhead c. **[critical path]**
- `counting_boundary_pick_two` — Compatible + injection bound + growth gap cannot all hold. **[critical path]**
- `standard_model_consistent_growth_gap` — standardModel has unbounded selfApp AND growth gap (coexistence). **[supplementary]**
- `unbounded_injection_bound_vacuous` — SelfAppUnbounded → HasInjectionBound holds vacuously (bounded construction leg fails). **[critical path]**
- `standardModel_separation_complete` — standardModel: unbounded + ¬PEqNP + growth gap + vacuous injection bound (four-part conjunction). **[critical path]**
- `trivialModel_compatible_complete` — trivialModel: Compatible + PEqNP + factors all grades (axiom empty). **[critical path]**
- `gradeGap_anti_compression_assembly` — full anti-compression through gradeGap: Compatible + injection bound kills growth gap; unbounded makes injection bound vacuous; standardModel witnesses consistency. **[critical path]**

**WTS/ReturnPath/Naming/SeparationLocalization.lean** — separation localized to positive-gap region.

- `overflow_witness_positive_gap` — every overflow witness has gradeGap > 0. **[critical path]**
- `nonpositive_gap_no_overflow` — elements with gradeGap ≤ 0 cannot be overflow witnesses. **[critical path]**
- `substrate_outside_gap_region` — Im(selfApp) has gradeGap = 0, outside the carrier gap region. **[critical path]**
- `separation_localized_to_positive_gap` — SelfAppUnbounded overflow witnesses all have gradeGap > 0. **[critical path]**
- `transport_model_no_separation` — SelfAppUnbounded impossible on transport model. **[critical path]**
- `separation_fully_localized` — four-part conjunction: substrate immune, transport model immune, finite carriers immune, separation localized to positive-gap complement. **[critical path]**

**WTS/ReturnPath/PartialReturn.lean** — subdomain return for Group B.

- `partialLambek_zero_gap` — on PartialLambekData domain, gradeGap = 0. **[critical path]**
- `partial_bridge_via_gradeGap` — cofinal zero-gap domain + SelfAppUnbounded => False. **[critical path]**
- `SubdomainDecomposition` — carrier = domain (gap=0) + complement (gap possibly nonzero). **[supplementary]**
- `full_domain_gives_lambek` — full coverage PartialLambekData gives LambekData. **[supplementary]**

**WTS/ReturnPath/Generator.lean** — Profile collapse + axiom strata.

- `canonical` — enriched tower profile of any GRM: FixedPointCost, SubstrateShape, EtaStatus, NamingEquivalence. **[critical path]**
- `profile_has_two_degrees_of_freedom` — enriched profile collapses to 2 propositions: (PEqNP?, selfApp = id?). Everything else derivable from roundtrip in one rewrite. Axioms: propext, Quot.sound. **[critical path]**
- `tower_complete` — positive chain at axiom level empty: five-part conjunction (surjection, Y fixed point, quine, beta, eta). Axioms: **none**. **[critical path]**
- `classification_dn` — three-way classification is irrefutable from pure logic. Axioms: **none**. **[critical path]**
- `classification_classical` — three-way classification of arbitrary GRM. Axioms: propext, Classical.choice, Quot.sound. **[critical path]**
- `four_strata` — tower + irrefutability + witnesses + PolyMarkov bridge, assembled. Axioms: propext, Quot.sound. **[critical path]**
- `polymarkov_peqnp` — if FactorsThrough is decidable and PolyMarkov holds, double-negation of PEqNP implies PEqNP. PolyMarkov enters as hypothesis, not kernel axiom. Axioms: **none**. **[critical path]**
- `unbounded_implies_not_peqnp` — forward direction: SelfAppUnbounded → ¬PEqNP. Constructive. Axioms: propext, Quot.sound. **[critical path]**
- `not_peqnp_implies_unbounded` — backward direction: ¬PEqNP → SelfAppUnbounded. Requires witness extraction. Axioms: propext, Classical.choice, Quot.sound. **[critical path]**
- `peqnp_iff_not_unbounded` — full equivalence. Axioms: propext, Classical.choice, Quot.sound. **[critical path]**
- `retractionModel` — concrete witness: PEqNP with selfApp ≠ id. Nat carrier, fold = ÷2, unfold = 2x, grade = id. **[critical path]**
- `bounded_not_from_eta` — bounded selfApp does not imply identity selfApp. retractionModel witnesses this. **[supplementary]**

**WTS/ReturnPath/Naming/DeficitEquivalence.lean** — Nat decomposition of gradeGap.

- `gradeDeficit` / `gradeShortfall` — upward cost and downward shift in Nat. **[critical path]**
- `nonpositive_gap_iff_zero_deficit` — Compatible iff zero deficit everywhere. **[critical path]**
- `deficit_trichotomy` — three regimes via Nat deficit, witnessed. **[supplementary]**

**WTS/ReturnPath/ConstructiveOmega.lean** — Y combinator at axiom level empty.

- `omega_fixed_point` — categorical Y combinator fixed-point equation. Axiom profile: **none** (zero axioms). **[supplementary]**
- `ReflCat` — minimal categorical vocabulary: monoidal closed category with curry/uncurry. **[supplementary]**
- `ReflData` — reflexive data: isomorphism [A, L] = L. **[supplementary]**

**WTS/ReturnPath/ReflexiveObject.lean** — Reflexive object: D = (D -> D).

- `ReflexiveObject` — structure with carrier D, fold : (D -> D) -> D, unfold : D -> (D -> D), both roundtrips. **[supplementary]**
- `selfApp_fold` — selfApp of fold(f) = f(fold(f)). **[supplementary]**
- `unfold_fold_id` — unfold(fold(id)) = id. **[supplementary]**
- `selfApp_fold_id` — selfApp(fold(id)) = fold(id). **[supplementary]**

**WTS/ReturnPath/FixedPointCombinator.lean** — Y combinator from reflexive object.

- `Y_fixed_point` — Y(f) = f(Y(f)) for any f : D -> D. **[supplementary]**
- `omegaSq_fixed_point` — omegaSq(f) = f(omegaSq(f)), equivalent to Y. **[supplementary]**
- `selfApp_omega` — selfApp(omega(f)) = f(selfApp(omega(f))). **[supplementary]**

**WTS/ReturnPath/Containerization.lean** — Closed container from reflexive object.

- `ClosedContainer` — structure with eval/name/beta/eta. **[supplementary]**
- `ReflexiveObject.toClosedContainer` — every reflexive object yields a closed container. **[supplementary]**
- `ClosedContainer.Y_fixed_point` — Y combinator in container form. **[supplementary]**
- `comp_assoc` — composition in closed containers is associative. **[supplementary]**

**WTS/ReturnPath/Naming/ReflexiveToGraded.lean** — GradedReflModel derived from reflexive structure.

- `FullReflexiveStructure` — full reflexive iso with both roundtrips. **[critical path]**
- `fullReflexive_selfApp_eq_id` — full iso forces selfApp = id. **[critical path]**
- `gradeGap` — grade gap: Int-valued measure of selfApp's grade change. **[critical path]**
- `fullReflexive_zero_gap` — full iso has zero grade gap. **[critical path]**
- `unbounded_gap_from_selfAppUnbounded` — SelfAppUnbounded implies unbounded positive gap. **[critical path]**
- `weakening_creates_separation` — unbounded selfApp implies not PEqNP. **[critical path]**
- `fullReflexive_always_collapse` — full iso always in collapse regime. **[critical path]**
- `grounding_summary` — full iso collapses, unbounded weakening separates, both witnessed. **[critical path]**

**Archived files** (in `archive/naming-supplementary/`, not in active build):
BLLBridge.lean, BLLTowerLevels.lean, GradedSubObjects.lean,
Level4PneNP.lean, ContainerRestriction.lean. All 0 sorry, propext +
Quot.sound only. Supplementary interpretive frameworks not on the
critical path.

### Transport Layer (10 files, assembled from pnp-integrated)

**WTS/Transport/WitnessTransportCore.lean** — Transport primitives.

- `Transport` — structure: move function with overhead. **[critical path]**
- `Projection` — structure: projection with certify/extract. **[critical path]**
- `Realizable` — element is realizable at grade d. **[critical path]**
- `Transport.consequenceClosed` — transport preserves grade bounds. **[critical path]**
- `consequence_closed_compose_pair` — consequence closure composes. **[critical path]**
- `identity_consequence_closed` — identity transport is consequence-closed. **[supplementary]**
- `projection_certify_from_fold_compat` — projection certify from fold compatibility. **[supplementary]**
- `projection_idempotent` — projection is idempotent. **[supplementary]**
- `projection_grade_bounded` — projection is grade-bounded. **[supplementary]**
- `transport_collapse_implies_grade_preserved` — transport collapse preserves grade. **[supplementary]**
- `transport_collapse_preserves_realizable` — transport collapse preserves realizability. **[supplementary]**
- `trivialModel_transport_collapse` — trivialModel has transport collapse. **[supplementary]**
- `projection_collapse_implies_bounded` — projection collapse implies bounded. **[supplementary]**

**WTS/Transport/ConsequenceClosureCore.lean** — Chain composition.

- `TransportChain` — chain of transports with overhead accumulation. **[critical path]**
- `consequence_closed_compose` — consequence closure composes over chains. **[critical path]**
- `two_step_consequence_closed` / `chain_two_consequence_closed` — two-step composition. **[supplementary]**
- `degradation_witness_implies_incoherent` / `degradation_implies_witness` — degradation characterization. **[supplementary]**
- `prefix_fullyConsequenceClosed` — prefix of closed chain is closed. **[supplementary]**
- `trivialModel_step_closed` / `trivialModel_all_closed` — trivialModel conservativity. **[supplementary]**

**WTS/Transport/TransportSelfSimilarity.lean** — Self-similarity and structural retraction.

Principal results (46 theorems total, 43 unconditional):
- `transportGradedReflModel` — transport structure yields a GRM with selfApp = id. **[critical path]**
- `transport_model_selfApp_eq_id` — THE TRANSPORT SELF-SIMILARITY THEOREM. selfApp = id for any transport-derived GRM. **[critical path]**
- `transport_model_PEqNP` — PEqNP holds in transport model. **[critical path]**
- `GRMorphism` / `GRRetraction` — morphism and retraction between GRMs. **[critical path]**
- `structural_retraction` — transport model retracts onto base model. **[critical path]**
- `PolyGRRetraction` — polynomial-bounded retraction. **[critical path]**
- `PolyGRRetraction.compose` — polynomial retractions compose. **[supplementary]**
- `transport_retraction_regime_forced` — retraction forces regime. **[supplementary]**
- `GRMorphism.reflects_factorsThrough` / `reflects_PEqNP` — morphisms reflect regime predicates. **[supplementary]**
- `trivial_transport_conservativity` — trivialModel transport conservativity. **[supplementary]**

**WTS/Transport/TransportCollapseObstruction.lean** — Collapse obstruction.

- `sideA_bounded_selector_impossible` — PROVED THEOREM: no bounded selector agrees with selfApp when unbounded. One-step consequence of `selfApp_not_factors`. **[critical path]**
- `faithful_zero_overhead_impossible` — zero overhead + faithfulness + SelfAppUnbounded -> False. Derives local bound from `h_grade_bound`. **[critical path]**
- `zero_overhead_not_faithful` — TransportFaithful is disprovable in the separation regime for any zero-overhead transport at any grade. **[critical path]**
- `trivialModel_faithful` — conservativity: trivialModel's identity transport IS faithful at every grade. **[supplementary]**
- `transport_collapse_grade_preserved` / `transport_collapse_implies_core_collapse` — collapse structure. **[supplementary]**
- `shortcut_to_collapse` — shortcut implies collapse. **[supplementary]**
- `trivialModel_not_obstructed` — trivialModel has no obstruction. **[supplementary]**

**WTS/Transport/AggregationDepthBarrier.lean** — Aggregation overhead.

- `AggregationScheme` / `ReplacementMechanism` / `ComplexityMeasure` — aggregation structures. **[supplementary]**
- `overhead_constitutivity` — overhead is constitutive (cannot be eliminated). **[critical path]**
- `no_static_certificate_replacement` — no static replacement mechanism can bypass aggregation depth. **[critical path]**
- `faithful_replacement_grade_bounded` / `faithful_composed_transport_bounded` — bounds on faithful replacements. **[supplementary]**
- `aggregation_propagates_realizability` — aggregation preserves realizability. **[supplementary]**
- `identityAggregation` / `trivialModel_zero_aggregation` — trivialModel aggregation. **[supplementary]**

**WTS/Transport/BindingStructure.lean** — Consequence binding.

- `ConsequenceBinding` / `CoherentField` — binding structures. **[supplementary]**
- `consequence_binding_bound` — binding propagates grade bounds. **[critical path]**
- `coherent_field_non_decomposable` — coherent fields are non-decomposable. **[critical path]**
- `consequence_closure_creates_binding` — closure creates binding. **[supplementary]**
- `trivialModel_consequence_binding_trivial` — trivialModel has trivial binding. **[supplementary]**

**WTS/Transport/ProjectionPreservation.lean** — Projection structure.

- `CompatibleProjection` / `ProjectionAsymmetry` — projection structures. **[supplementary]**
- `compatible_preserves_certify` — compatible projection preserves certification. **[supplementary]**
- `projection_grade_stable` — projection grades are stable. **[critical path]**
- `projection_idempotent_pp` / `projection_grade_monotone` — projection properties. **[supplementary]**
- `trivialModel_no_asymmetry` — trivialModel has no projection asymmetry. **[supplementary]**

**WTS/Transport/BridgeNecessity.lean** — Bridge necessity.

- `MeasureBridge` / `ConsequenceBridge` / `GroundedBridge` — bridge structures. **[supplementary]**
- `measure_bridge_compatible_with_both_regimes` — measure bridges exist in both regimes. **[critical path]**
- `consequence_enables_grounding` — consequence bridges enable grounding. **[supplementary]**
- `transfer_witnesses_consequence` — transfer witnesses consequence structure. **[supplementary]**
- `commutativity_summary` — bridge commutativity characterization. **[supplementary]**

**WTS/Transport/OmegaChainCompletion.lean** — Omega-chain and Lambek data.

- `GRMEndofunctor` — endofunctor on GRM. **[critical path]**
- `GRMEndofunctor.F_PEqNP` / `FF_collapse` / `FF_PEqNP` — endofunctor forces PEqNP. **[critical path]**
- `GRMEndofunctor.regime_forced` / `structural_retraction` — regime forcing via retraction. **[critical path]**
- `LambekData` — full Lambek data (encode/decode are inverse). **[critical path]**
- `LambekData.selfApp_eq_id` — Lambek data forces selfApp = id. **[critical path]**
- `LambekData.PEqNP` — Lambek data implies PEqNP. **[critical path]**
- `bridge_factory` — endofunctor yields bridge. **[critical path]**
- `lambek_factory` — endofunctor yields Lambek data. **[critical path]**
- `PartialLambekData` — partial Lambek data on a subdomain. **[critical path]**
- `transportEndofunctor` / `transportEndofunctor_recovers_fixed_point` — transport-derived endofunctor. **[supplementary]**

**WTS/Transport/ObstructionInvariance.lean** — Pushforward/pullback.

- `PartialLambekData.pushforward` / `pushforward_strict` — pushforward of partial Lambek data along morphisms. **[supplementary]**
- `GRMorphism.comp` — morphism composition. **[supplementary]**

### Shared Layer (5 files, assembled from classical-constraints)

**WTS/Shared/Basic.lean** — Instance family definitions.

- `InstanceFamily` — family of problem instances with solutions and satisfiability. **[critical path]**

**WTS/Shared/SATPresheafCore.lean** — SAT instances and gluing.

- `SATInstance` — SAT formula with variables, clauses, evaluation. **[critical path]**
- `LocalSection` / `GlobalSection` — local and global assignments. **[critical path]**
- `gluing_iff_satisfiable` — gluing local sections is equivalent to satisfiability. **[critical path]**
- `satisfiable_implies_gluing` / `gluing_implies_satisfiable` — both directions. **[supplementary]**
- `empty_satisfiable` / `empty_clause_unsat` / `unit_clause_sat` / `contradiction_unsat` — concrete examples. **[supplementary]**

**WTS/Shared/CookSelectorBridge.lean** — Bounded selector from poly-time solver.

- `BoundedSelector` — bounded resource selector for SAT instances. **[critical path]**
- `PolyTimeSolver` — polynomial-time SAT solver. **[critical path]**
- `poly_solver_induces_bounded_selector` — poly-time solver yields bounded selector. **[critical path]**
- `capacity_gap_implies_blind_spots` — capacity gap between selector and instance implies blind spots. **[critical path]**
- `bounded_selector_correct` / `bounded_selector_ext` / `bounded_selector_detects_sat` — selector properties. **[supplementary]**
- `BoundedSelector.localEquiv` — equivalence relation on bounded selectors. **[supplementary]**
- `localEquiv_refl` / `localEquiv_symm` / `localEquiv_trans` — equivalence properties. **[supplementary]**

**WTS/Shared/CookFaithfulness.lean** — Cook encoding and faithfulness.

- `CookEncoding` — encoding of SAT into model with polynomial grade bound. **[critical path]**
- `ObstructionProfile` — obstruction depth profiles. **[critical path]**
- `identityEncoding` — the identity encoding. **[supplementary]**
- `encoding_grade_bounded` — encodings are grade-bounded. **[supplementary]**
- `poly_bound_monotone` — polynomial bounds are monotone. **[supplementary]**

**WTS/Shared/SideAMirror.lean** — Mirror types from constructive side.

Mirror structures (14 exact matches with pnp-integrated):
- `GradedReflModel_Mirror`, `SelfAppUnbounded_Mirror`, `FactorsThrough_Mirror`, `PEqNP_Mirror`, `Realizable_Mirror`, `GRMorphism_Mirror`, `GRRetraction_Mirror`, `PolyGRRetraction_Mirror`, `LambekData_Mirror`, `PartialLambekData_Mirror`, `RelevantSubdomain_Mirror`, `GRMEndofunctor_Mirror`

Proved theorem:
- `selfApp_nonincreasing_contradiction` — if selfApp is unbounded, no grade-non-increasing function can agree with it everywhere. Used by Path 2 (direct bridge). **[critical path]**

Axiom:
- `sideA_bounded_selector_impossible_mirror` — mirrors proved theorem from Transport layer. See Section 2. **[critical path]**

Mirror theorems (derived from mirror structures, unconditional given the structure parameters):
- `GRMorphism_Mirror.map_selfApp`, `reflects_factorsThrough`, `reflects_PEqNP` — morphism properties on mirror types. **[supplementary]**
- `GRMEndofunctor_Mirror.F_PEqNP`, `FF_collapse`, `regime_forced`, `structural_retraction` — endofunctor properties on mirror types. **[supplementary]**
- `LambekData_Mirror.selfApp_eq_id`, `PEqNP` — Lambek properties on mirror types. **[supplementary]**
- `bridge_factory_mirror` / `lambek_factory_mirror` — factory theorems on mirror types. **[supplementary]**

### Protocol Layer (8 files, 7 assembled from classical-constraints + 1 bridge)

**WTS/Protocol/DistributedWitnessCore.lean** — Distributed witness system.

- `DistributedWitnessSystem` — four primitives: localCertify, transport, project, realize. **[critical path]**
- `WitnessPath` — inductive type for witness transport paths. **[critical path]**
- `TransportCollapse` / `ProjectionCollapse` / `ValueCollapse` — three collapse notions. **[critical path]**
- `Forgeable` / `Launderable` / `AggregationFailure` / `WitnessExpropriation` / `PanopticonAsymmetry` / `ProjectionCapture` — six failure modes. **[critical path]**
- `WitnessSovereignty` — witnesses remain under participant control. **[critical path]**
- `witness_sovereignty_from_closure` — sovereignty follows from closure conditions. **[critical path]**
- `witnessPath_cost_bound` / `witnessPath_refl_overhead` — path cost bounds. **[supplementary]**
- `projection_not_implies_value` — projection collapse does not imply value collapse. **[supplementary]**
- `aggregation_from_realizable_global` — aggregation from globally realizable witnesses. **[supplementary]**
- `forgeable_not_implies_launderable` — forgeability does not imply launderability. **[supplementary]**
- `trivial_value_collapse` — trivial value collapse exists. **[supplementary]**
- `witnessPath_concat_length` — path concatenation length. **[supplementary]**

**WTS/Protocol/CapabilityWitnessInstance.lean** — Capability witness system.

- `capabilityWitnessSystem` — concrete DistributedWitnessSystem for capabilities. **[critical path]**
- `delegation_overhead_is_one` — delegation adds exactly one unit of overhead. **[supplementary]**
- `delegation_is_transport` — delegation IS transport. **[supplementary]**
- `active_cap_locally_certified` — active capabilities are locally certified. **[supplementary]**
- `capability_no_transport_collapse` — capability system has no transport collapse. **[critical path]**
- `capability_projection_collapse` — capability system has projection collapse. **[critical path]**
- `capability_no_value_collapse` — capability system has no value collapse. **[critical path]**
- `transport_depth_increment` / `witnessPath_depth_bound` / `realizable_depth_bounded` — depth bounds. **[supplementary]**
- `projection_activates` / `projection_preserves_depth` / `projection_preserves_holder` — projection properties. **[supplementary]**

**WTS/Protocol/ZKProjectionInstance.lean** — Zero-knowledge witness system.

All theorems in this file are parameterized by `ZKSystem` (see Section 4).

**WTS/Protocol/CoherenceTransportMeasure.lean** — Coherence measure.

All theorems in this file are parameterized by `CoherenceMeasure` (see Section 4).

**WTS/Protocol/ValueCollapseInstance.lean** — Value collapse.

All theorems in this file are parameterized by `ScalarProxy` or `NonExtractiveValueSystem` (see Section 4).

**WTS/Protocol/ProtocolWitnessFamilyLock.lean** — Lock theorem.

- `ProtocolWitnessFamily` — five protocol regimes as one structure. **[critical path]**

Conditional theorems documented in Section 4.

**WTS/Protocol/ProtocolGRMBridge.lean** — Bridge from DWS to GRM.

- `ProtocolGRM` — structure: DWS + language/model agents + encode/decode with roundtrip. Chain 7's carrier engineering gap made precise. **[critical path]**
- `ProtocolGRM.toGRM` — induced GRM (carrier = State, fold = encode, unfold = decode, grade = cost). **[critical path]**
- `ProtocolGRM.HasCotrip` — the open condition: decode(encode(x)) = x. **[critical path]**
- `ProtocolGRM.cotrip_groupC` — cotrip → selfApp = id ∧ gradeGap = 0 ∧ Compatible ∧ PEqNP. **[critical path]**
- `coherence_gradeGap_bridge` — cotrip + max coherence on both directions → protocol-level consequence closure + GRM-level Group C. THE bridge theorem. **[critical path]**
- `protocol_gradeGap_is_roundtrip_cost` — gradeGap = cost(decode(encode(s))) - cost(s) (axiom empty). **[critical path]**
- `protocol_gradeGap_bounded` — gradeGap ≤ 2 * transportOverhead (without cotrip). **[supplementary]**
- `max_coherence_encode` / `max_coherence_decode` — max coherence → consequence closure per direction. **[supplementary]**

**WTS/Protocol/ConsensusWitnessInstance.lean** — Consensus witness system.

- `trivial_fc_zero_depth` — trivial finality condition has zero depth. **[supplementary]**

All other theorems in this file are parameterized by `FinalityCondition` (see Section 4).

---

## 4. What Is Proved (Conditional)

Every theorem listed below depends on one or more open hypotheses carried as parameters. This is standard mathematical practice: the theorem says "if X then Y."

### Lock theorem (Protocol layer)

- **`WTS.no_bounded_protocol_shortcuts`**
  - File: `WTS/Protocol/ProtocolWitnessFamilyLock.lean`
  - Hypotheses: `ConsequenceFaithful enc`, `ProtocolTransfer M family enc cf` (both uninhabitable via BridgeVacuity — transfer uninhabitable in TC models)
  - Says: assuming the protocol encoding is consequence-faithful and transfers to the model, a poly-time SAT solver leads to contradiction via the mirror axiom. BridgeVacuity makes this regime-characterizing (hypotheses jointly unsatisfiable) for TC models.
  - Shared with: this is the principal conditional result. ConsequenceFaithful and ProtocolTransfer are used only here. Both are moot in TC models.

### Sovereignty (Protocol layer)

- **`WTS.sovereignty_from_closure`**
  - File: `WTS/Protocol/ProtocolWitnessFamilyLock.lean`
  - Open hypotheses: explicit closure conditions as function parameters (h_cert, h_closed, h_agg)
  - Says: witness sovereignty holds for any system where certification implies realization, transport is consequence-closed, and aggregation is closed.

- **`WTS.sovereignty_implies_transport_closed`** / **`sovereignty_implies_agg_closure`**
  - File: `WTS/Protocol/DistributedWitnessCore.lean`
  - Open hypothesis: `WitnessSovereignty S participants`
  - Says: sovereignty implies transport closure and aggregation closure.

### Collapse relations (Protocol layer)

- **`WTS.value_collapse_implies_projection`**
  - File: `WTS/Protocol/DistributedWitnessCore.lean`
  - Open hypotheses: value collapse + cost condition
  - Says: value collapse implies projection collapse under cost monotonicity.

- **`WTS.transport_collapse_implies_projection_conditional`**
  - File: `WTS/Protocol/DistributedWitnessCore.lean`
  - Open hypotheses: transport collapse + projection identity condition
  - Says: transport collapse implies projection collapse when projection is identity.

### Transport obstruction theorems

- **`WTS.selfAppUnbounded_obstructs_transport_collapse`**
  - File: `WTS/Transport/TransportCollapseObstruction.lean`
  - Hypotheses: `SelfAppUnbounded M`, `TransportFaithful` (faithfulness bridge)
  - Says: unbounded selfApp obstructs transport collapse when transport is faithful.

- **`WTS.selfAppUnbounded_no_shortcut`**
  - File: `WTS/Transport/TransportCollapseObstruction.lean`
  - Hypotheses: `SelfAppUnbounded M`, `TransportFaithful`
  - Says: no transport shortcut exists when selfApp is unbounded.

- **`WTS.faithful_transport_impossible`**
  - File: `WTS/Transport/TransportCollapseObstruction.lean`
  - Hypothesis: `SelfAppUnbounded M`
  - Says: faithful transport is impossible when selfApp is unbounded.

### Aggregation theorems

- **`WTS.selfApp_aggregation_no_replacement`**
  - File: `WTS/Transport/AggregationDepthBarrier.lean`
  - Hypothesis: `SelfAppUnbounded M`
  - Says: no replacement mechanism can bypass selfApp aggregation when unbounded.

- **`WTS.selfAppUnbounded_obstructs_collapse_conditional`**
  - File: `WTS/Transport/AggregationDepthBarrier.lean`
  - Hypotheses: `SelfAppUnbounded M`, faithfulness bridge
  - Says: unbounded selfApp obstructs collapse conditional on faithfulness.

### Projection theorems

- **`WTS.projection_blocks_extract_when_retraction`** / **`projection_blocks_extract_when_unbounded`**
  - File: `WTS/Transport/WitnessTransportCore.lean`
  - Hypothesis: `SelfAppUnbounded M`
  - Says: projection blocks extraction when selfApp is unbounded.

- **`WTS.projection_blocks_extract_nontrivial`** / **`projection_asymmetry_exists`**
  - File: `WTS/Transport/ProjectionPreservation.lean`
  - Hypothesis: `SelfAppUnbounded M`
  - Says: nontrivial projection asymmetry exists when selfApp is unbounded.

### Self-similarity theorems

- **`WTS.selfApp_no_bounded_transport`**
  - File: `WTS/Transport/TransportSelfSimilarity.lean`
  - Hypothesis: `SelfAppUnbounded M`
  - Says: no bounded transport for selfApp when unbounded.

- **`WTS.base_vs_transport_contrast`**
  - File: `WTS/Transport/TransportSelfSimilarity.lean`
  - Hypothesis: `SelfAppUnbounded M`
  - Says: base model and transport model have contrasting regime status.

- **`WTS.strict_morphism_propagates_separation`**
  - File: `WTS/Transport/TransportSelfSimilarity.lean`
  - Hypothesis: `SelfAppUnbounded M₁`
  - Says: strict morphisms propagate separation.

### Bridge necessity theorems

- **`WTS.Transport.BridgeNecessity.grounded_overflowing_implies_separation`**
  - File: `WTS/Transport/BridgeNecessity.lean`
  - Hypothesis: source depth overflow condition
  - Says: grounded overflowing bridge implies separation.

- **`WTS.Transport.BridgeNecessity.no_transfer_when_unbounded`** / **`consequence_is_only_bridge_form`**
  - File: `WTS/Transport/BridgeNecessity.lean`
  - Hypothesis: `SelfAppUnbounded M`
  - Says: no transfer when unbounded; consequence is the only bridge form.

### Partial bridge theorems

- **`WTS.partial_bridge`**
  - File: `WTS/Transport/OmegaChainCompletion.lean`
  - Hypotheses: `RelevantSubdomain M`, `SelfAppUnbounded M`
  - Says: partial Lambek data on a relevant subdomain obstructs separation.

- **`WTS.partial_bridge_mirror`**
  - File: `WTS/Shared/SideAMirror.lean`
  - Hypotheses: `RelevantSubdomain_Mirror M`, `SelfAppUnbounded_Mirror M`
  - Says: mirror version of partial bridge.

- **`WTS.partial_bridge_invariant`** / **`partial_bridge_invariant_transitive`** / **`obstruction_propagates_separation`**
  - File: `WTS/Transport/ObstructionInvariance.lean`
  - Hypotheses: `RelevantSubdomain M₁`, `GRMorphism`, surjectivity, `SelfAppUnbounded`
  - Says: partial bridge is invariant under pushforward along surjective morphisms.

### Consensus witness theorems (parameterized by FinalityCondition)

- **`WTS.consensusWitnessSystem`**, **`consensus_transport_depth`**, **`consensus_no_transport_collapse`**, **`consensus_sovereignty`**, **`consensus_projection_collapse`**, **`expropriation_breaks_sovereignty`**
  - File: `WTS/Protocol/ConsensusWitnessInstance.lean`
  - Open parameter: `FinalityCondition`
  - Says: consensus witness system properties hold for any finality condition.

### ZK witness theorems (parameterized by ZKSystem)

- **`WTS.zkWitnessSystem`**, **`zk_has_transport_collapse`**, **`zk_preserves_certify`**, **`zk_has_projection_collapse`**, **`zk_no_value_collapse`**, **`zk_blocks_extract`**, **`zk_projection_zeroes_cost`**, **`zk_not_launderable`**
  - File: `WTS/Protocol/ZKProjectionInstance.lean`
  - Open parameter: `ZKSystem`
  - Says: ZK witness system properties hold for any ZK system.

### Coherence measure theorems (parameterized by CoherenceMeasure)

- **`WTS.coherence_bounded`**, **`coherence_refl`**, **`coherence_max_implies_closed`**, **`below_threshold_has_degraded_step`**, **`full_coherence_composes`**, and 12 others
  - File: `WTS/Protocol/CoherenceTransportMeasure.lean`
  - Open parameter: `CoherenceMeasure`
  - Says: coherence properties hold for any quantitative coherence measure.

### Value collapse theorems (parameterized by ScalarProxy / NonExtractiveValueSystem)

- **`WTS.price_is_projection`**, **`consequence_closed_path_realizes`**, **`coherence_value_is_max_when_closed`**, **`no_value_collapse_from_witness`**
  - File: `WTS/Protocol/ValueCollapseInstance.lean`
  - Open parameters: `ScalarProxy`, `NonExtractiveValueSystem`
  - Says: value collapse properties hold for any scalar proxy or non-extractive value system.

### Cook faithfulness theorems (parameterized by encoding)

- **`WTS.CookFaithful`**, **`faithful_lower_bound`**, **`faithful_upper_bound`**, **`trivialFaithful`**, **`equalDepthFaithful`**
  - File: `WTS/Shared/CookFaithfulness.lean`
  - Open parameter: `CookEncoding`
  - Says: faithfulness properties hold for any Cook encoding.

### Capability witness theorems with open hypotheses

- **`WTS.consequence_closure_implies_realizable`**
  - File: `WTS/Protocol/CapabilityWitnessInstance.lean`
  - Hypothesis: consequence-closed chain
  - Says: consequence closure implies realizability.

- **`WTS.laundered_capability_unrealizable`**
  - File: `WTS/Protocol/CapabilityWitnessInstance.lean`
  - Hypothesis: delegation depth exceeds bound
  - Says: laundered capabilities are unrealizable.

### Binding structure theorems with open hypotheses

- **`WTS.coherent_field_creates_binding`** / **`coherent_field_non_independent`**
  - File: `WTS/Transport/BindingStructure.lean`
  - Hypothesis: field size ≥ 2
  - Says: coherent fields of size ≥ 2 create bindings and are non-independent.

---

## 5. What Is NOT Claimed

This section addresses the most likely misreadings a reviewer would have.

**This project does NOT claim P ≠ NP.** The lock theorem (`no_bounded_protocol_shortcuts`) is conditional on `ConsequenceFaithful` and `ProtocolTransfer`. These conditions are carried as parameters. However, BridgeVacuity (proved in classical-constraints/BridgeVacuity.lean) shows the transfer mechanism is uninhabitable in any TC model: `transfer_hypothesis_uninhabitable` proves TransferHypothesis + SelfAppUnbounded → False. The lock theorem is regime-characterizing (hypotheses jointly unsatisfiable) for TC models. The bridge condition IS the regime question (`transfer_hypothesis_characterization`).

**The ULC is NOT a universal object in the categorical sense.** It is a minimal abstraction — two types, two maps, no axioms — that serves as the type whose instances are the collection of language-model pairings. It has no universal property, no initiality, no terminality.

**The "collection" has no topology, metric, or morphisms between instances unless explicitly stated.** The ULC defines what a language-model pairing IS. The collection of all ULC instances is combinatorially unbounded. No structure on the collection (topology, distance, arrows between instances) is assumed or proved beyond what is explicitly stated.

**The gap theorem establishes that bounded-idempotent does NOT force identity — it does not determine which regime holds at any specific instance.** The `bounded_idempotent_not_forces_identity` theorem witnesses the gap with a concrete model (`retractionModel`). This shows the gap EXISTS. It does not resolve which side of the gap any particular language-model pairing falls on. The carrier engineering gap at each Group B chain is now resolved via the CanonicalMirror framework (PartialMirrorAdequacy.lean, ChainInstantiation.lean): the bridge arguments go through on CanonicalMirror without requiring a full GRM whose selfApp equals the canonicalizer.

**Conservativity is the point, not a weakness.** Both regimes (selfApp = id and SelfAppUnbounded) are witnessed by concrete models (`trivialModel` and `standardModel`). This proves that any single language-model pairing is trivially answerable. The contribution is the structure of the collection — which predicates hold where and what constraints any resolution must satisfy — not resolving one instance.

**The mirror axiom is proved.** The axiom `sideA_bounded_selector_impossible_mirror` in `SideAMirror.lean` mirrors the proved theorem `sideA_bounded_selector_impossible` in `TransportCollapseObstruction.lean`. The two are character-identical modulo `_Mirror` suffixes. The mirroring exists because the constructive and classical layers cannot share imports. This is an architectural choice documented in BRIDGE_PATH_TABLE.md, not an unverified assumption.

**Single language-model pairings are trivially answerable.** This is proved by conservativity. The contribution of the program begins where single-point answers end: the structure of the entire collection, the three-group classification, and the canonical carrier architecture. The ProjectionalAtlas (ProjectionalAtlas.lean) shows every natural semantic archetype across all seven chains is projectional and lands in PEqNP (or Group C); the boundary against standardModel is invariant under BoundedGRMEquiv.

**SelfAppUnbounded is NOT an encoding-invariant quantity.** The exact `SelfAppUnbounded` threshold, strict extension (drift 0), and the exact `PEqNP` boundary are presentation-sensitive: they shift under bounded-overhead reencoding (`BoundedGRMEquiv`). The encoding-invariant obstructions are `UnboundedGap` (no finite drift exists) and `FiniteDrift` (some finite drift exists). Least drift is stable to within `2c` under overhead `c`. When the project refers to "the obstruction," the encoding-invariant form (`UnboundedGap` / `FiniteDrift`) is the robust semantic quantity; `SelfAppUnbounded` is a presentation coordinate.

**The three-group classification is a predicate partition, not a narrative.** Groups A, B, and C are distinguished by which predicates hold: whether selfApp = id (Group C), whether ModelData is available with a grade-non-increasing `red` function (Group B), or neither (Group A). No interpretive claim is made about why groups differ — the difference is stated as predicate satisfaction.

---

## 6. Bridge Conditions Catalog

Every bridge condition in the project, named and typed. BridgeVacuity
(classical-constraints/BridgeVacuity.lean) proves that TransferHypothesis
is uninhabitable in TC models (`transfer_hypothesis_uninhabitable`).
All conditions below that feed into TransferHypothesis are therefore
uninhabitable for the TM case — the bridge condition IS the regime question.

### ConsequenceFaithful

- **Structure**: `WTS.ConsequenceFaithful`
- **File**: `WTS/Protocol/ProtocolWitnessFamilyLock.lean`
- **Parameter**: `enc : CookEncoding`
- **Fields**: `profile : ObstructionProfile`, `h_lower` (polynomial lower bound on depth), `h_upper` (polynomial upper bound on depth), `h_consequence` (consequence preservation)
- **Status**: uninhabitable in TC models. BridgeVacuity proves the transfer mechanism feeding from ConsequenceFaithful (via CookFaithful) is uninhabitable when SelfAppUnbounded holds. The lock theorem is regime-characterizing (hypotheses jointly unsatisfiable). Non-vacuously satisfiable as a standalone structure (`trivialConsequenceFaithful`), but this is irrelevant since the downstream transfer cannot be constructed.
- **Used by**: `no_bounded_protocol_shortcuts`

### ProtocolTransfer

- **Structure**: `WTS.ProtocolTransfer`
- **File**: `WTS/Protocol/ProtocolWitnessFamilyLock.lean`
- **Parameters**: `M : GradedReflModel_Mirror`, `family : SATFamily`, `enc : CookEncoding`, `cf : ConsequenceFaithful enc`
- **Fields**: `transfer` — function mapping bounded selector to grade-bounded model evaluator
- **Status**: uninhabitable in TC models. BridgeVacuity: `transfer_hypothesis_uninhabitable` proves TransferHypothesis + SelfAppUnbounded → False. The transfer mechanism cannot be constructed in any model where selfApp is unbounded.
- **Used by**: `no_bounded_protocol_shortcuts`

### CookFaithful

- **Structure**: `WTS.CookFaithful`
- **File**: `WTS/Shared/CookFaithfulness.lean`
- **Parameter**: `enc : CookEncoding`
- **Fields**: `profile : ObstructionProfile`, `h_lower`, `h_upper`
- **Status**: uninhabitable in TC models (BridgeVacuity). Satisfiable as standalone structure but downstream transfer uninhabitable under SelfAppUnbounded. ConsequenceFaithful implies CookFaithful via `consequenceFaithful_to_cookFaithful`.
- **Used by**: conditional theorems in CookFaithfulness.lean

### TransportFaithful

- **Definition**: `WTS.TransportFaithful`
- **File**: `WTS/Transport/TransportCollapseObstruction.lean`
- **Type**: property of a transport relating it to selfApp behavior
- **Status**: Open as standalone property. Not uninhabitable in TC models (unlike TransferHypothesis/ModelData). Used in conditional obstruction: TransportFaithful + bounded transport + SelfAppUnbounded → False. The faithfulness itself is compatible with TC; it's the combination with boundedness that contradicts.
- **Used by**: `selfAppUnbounded_obstructs_transport_collapse`, `selfAppUnbounded_no_shortcut`, `selfAppUnbounded_obstructs_collapse_conditional`

### RelevantSubdomain / RelevantSubdomain_Mirror

- **Structure**: `WTS.RelevantSubdomain` / `WTS.RelevantSubdomain_Mirror`
- **Files**: `WTS/Transport/OmegaChainCompletion.lean` / `WTS/Shared/SideAMirror.lean`
- **Status**: uninhabitable in TC models. Requires partial Lambek data + cofinality for separation witnesses; cotrip + cofinality contradicts SelfAppUnbounded.
- **Used by**: `partial_bridge`, `partial_bridge_mirror`, `partial_bridge_invariant`

### AdmissibleEncoding

- **Structure**: `WTS.AdmissibleEncoding`
- **File**: `WTS/Tower/CarrierEngineering/AdmissibleBridge.lean`
- **Fields**: carrier Names, fold/unfold with roundtrip, grade with bounded overhead, selfApp_bounded
- **Status**: The clean interface condition for classical semantics. Induces a GRM (toGRM). Admits drift at its overhead. Does NOT require axiomatizing "polynomial time" or "Turing machines" — requires exactly the data that induces a GRM with bounded grade distortion.
- **Used by**: `SameSemantics`, `carrier_architecture_unique`

### SameSemantics

- **Structure**: `WTS.SameSemantics`
- **File**: `WTS/Tower/CarrierEngineering/AdmissibleBridge.lean`
- **Parameters**: two `AdmissibleEncoding`s of the same domain
- **Fields**: bounded translations (translate/translate_back) commuting with selfApp; refl/symm/trans
- **Status**: Bridge interface. `SameSemantics.toBoundedGRMEquiv` proves that same-semantics encodings induce `BoundedGRMEquiv`, transferring all encoding-invariant properties. The remaining external obligation is whether classical polynomial-time encodings satisfy this condition.
- **Used by**: `toBoundedGRMEquiv`, `unboundedGap_iff`, `finiteDrift_iff`

### BoundedGRMEquiv

- **Structure**: `WTS.BoundedGRMEquiv`
- **File**: `WTS/Tower/CarrierEngineering/ReencodingInvariance.lean`
- **Fields**: carrier bijection (f, g, gf, fg) with bounded additive grade distortion (overhead c) and selfApp compatibility (f_compat)
- **Status**: The equivalence relation on GRMs for "same semantics, different encoding." Proved: UnboundedGap invariant (iff), FiniteDrift invariant (iff), least-drift stability (|k-k'| <= 2c), fixed-point subdomain bijection, groupoid structure. NOT invariant: SelfAppUnbounded, strict extension, exact PEqNP threshold.
- **Used by**: all encoding invariance results, `SameSemantics.toBoundedGRMEquiv`

### CoherenceMeasure

- **Structure**: `WTS.CoherenceMeasure`
- **File**: `WTS/Protocol/CoherenceTransportMeasure.lean`
- **Fields**: quantitative measure on transport steps with monotonicity
- **Status**: Protocol-internal parameter; uninhabitable for bridge purposes in TC models. No concrete instantiation provided.
- **Used by**: all theorems in CoherenceTransportMeasure.lean

### NonExtractiveValueSystem

- **Structure**: `WTS.NonExtractiveValueSystem`
- **File**: `WTS/Protocol/ValueCollapseInstance.lean`
- **Status**: Protocol-internal parameter; uninhabitable for bridge purposes in TC models. Conceptually load-bearing (characterizes non-extractive value), no concrete instantiation.
- **Used by**: `consequence_closed_path_realizes`

### FinalityCondition

- **Structure**: `WTS.FinalityCondition`
- **File**: `WTS/Protocol/ConsensusWitnessInstance.lean`
- **Status**: Protocol-internal parameter; uninhabitable for bridge purposes in TC models. Required to instantiate consensus witness system.
- **Used by**: `consensusWitnessSystem`, all consensus theorems

### ZKSystem

- **Structure**: `WTS.ZKSystem`
- **File**: `WTS/Protocol/ZKProjectionInstance.lean`
- **Status**: Protocol-internal parameter; uninhabitable for bridge purposes in TC models. Required to instantiate ZK witness system.
- **Used by**: `zkWitnessSystem`, all ZK theorems

---

## 7. File Inventory

**70 Lean files total**, categorized by role.

### ULC Refinement Tower (`WTS/Tower/`) — 13 files

| File | Role | Theorems | sorry |
|---|---|---|---|
| `WTS.lean` | Root import | 0 | 0 |
| `WTS/Tower/UniversalLanguageComputer.lean` | ULC definition + idempotence | 3 | 0 |
| `WTS/Tower/ClassicalModels.lean` | GRM embeds as ULC | 7 | 0 |
| `WTS/Tower/GradedULC.lean` | Graded ULC predicates | 5 | 0 |
| `WTS/Tower/ForcingPredicates.lean` | Gap theorem + three regimes | 10 | 0 |
| `WTS/Tower/FiniteCarrier.lean` | Finite-carrier theorem | 7 | 0 |
| `WTS/Tower/CarrierEngineering.lean` | Three-group classification | 5 | 0 |
| `WTS/Tower/CarrierEngineering/ProjectionObstruction.lean` | Projection obstruction for Group B | 9 | 0 |
| `WTS/Tower/CarrierEngineering/CanonicalMirror.lean` | Canonical mirror structure | 9 | 0 |
| `WTS/Tower/CarrierEngineering/PartialMirrorAdequacy.lean` | Bridge adequacy for CanonicalMirror | 16 | 0 |
| `WTS/Tower/CarrierEngineering/ChainInstantiation.lean` | Chain instantiation pattern | 14 | 0 |
| `WTS/Tower/CarrierEngineering/ReflectiveCarrierData.lean` | Master carrier structure (3 layers) | ~50 | 0 |
| `WTS/Tower/CarrierEngineering/SplitIdempotent.lean` | Split-idempotent equivalence | 20 | 0 |
| `WTS/Tower/CarrierEngineering/UniversalProperty.lean` | Universal property, carrier forced | 25 | 0 |
| `WTS/Tower/CarrierEngineering/DefectSpectrum.lean` | Defect as pointwise naming loss | 35 | 0 |
| `WTS/Tower/CarrierEngineering/LeastDrift.lean` | Least drift, stability theorem | 27 | 0 |
| `WTS/Tower/CarrierEngineering/DynamicDrift.lean` | Grade-dependent drift functions, actualDriftFn, encoding invariance | ~35 | 0 |
| `WTS/Tower/CarrierEngineering/ReencodingInvariance.lean` | Encoding-invariant obstructions | 30 | 0 |
| `WTS/Tower/CarrierEngineering/AdmissibleBridge.lean` | Interface to classical semantics | 17 | 0 |
| `WTS/Tower/CarrierEngineering/MinimalNecessityGradient.lean` | Theorem complex packaging | 7 | 0 |
| `WTS/Tower/FixedPointClassification.lean` | Transport model satisfies Group C | 3 | 0 |

Tower axiom profile: axiom-free (projection_forces_PEqNP, carrier_engineering_dilemma, partial_mirror_complete_bridge, roundtrip_selfApp_idempotent, canonicalize_idempotent, splitIdempotent_roundtrip, image_eq_fixed, carrier_architecture_unique, factorization, unboundedGap_iff_defect_unbounded, SameSemantics.toBoundedGRMEquiv, DynamicDriftCarrier definition); propext + Quot.sound (iff-theorems: grade_compatible_extension_iff, drift_extension_iff, defectBounded_iff_drift, leastDrift_stability, unboundedGap_iff, finite_drift_iff, drift_transport, projectional_no_unboundedGap, dynamic_drift_extension_iff, dynamic_drift_transport_mono, and older tower files); propext + Classical.choice + Quot.sound (unbounded_gap_iff_no_finite_drift, exists_least_drift, actualDriftFn, leastDriftAt, actualDriftFn_mono); Quot.sound only (FixedPointClassification). No Mathlib. No custom axioms.

### Return Path (`WTS/ReturnPath/`) — 15 root files + 13 Naming/ files

**Root files (positive chain + substrate + generator):**

| File | Role | Key results |
|---|---|---|
| `WTS/ReturnPath/GrammarFixedPoint.lean` | Grammar-level fixed point | `GCat`, `M_GCat_is_GCat` |
| `WTS/ReturnPath/ConstructiveOmega.lean` | Y combinator (axiom empty) | `omega_fixed_point` |
| `WTS/ReturnPath/ReflexiveObject.lean` | Reflexive object D = (D->D) | `selfApp_fold`, `unfold_fold_id` |
| `WTS/ReturnPath/FixedPointCombinator.lean` | Y combinator | `Y_fixed_point`, `omegaSq_fixed_point` |
| `WTS/ReturnPath/Containerization.lean` | Closed container | `ClosedContainer.Y_fixed_point`, `comp_assoc` |
| `WTS/ReturnPath/LambdaModel.lean` | Lambda model (beta+eta) from ReflData | `reflData_beta`, `reflData_eta` |
| `WTS/ReturnPath/IdentityLoop.lean` | Quine self-recognition | `quine_self_recognition`, `omega_at_identity` |
| `WTS/ReturnPath/SelfIndexedComputation.lean` | Self-indexed computation | `self_indexed_kleene`, `selfApp_recovers_named` |
| `WTS/ReturnPath/WeakReflData.lean` | Computation/naming boundary | `weak_omega_fixed_point`, `weakBeta` |
| `WTS/ReturnPath/InvariantSubstrate.lean` | Im(selfApp) invariant substrate | `InvariantSubstrate.ofSelfApp`, `substrate_zero_gap` |
| `WTS/ReturnPath/SubstrateComputation.lean` | Universal computation on substrate | `substrate_universal_computation`, `separation_regime_has_substrate` |
| `WTS/ReturnPath/StandardModelSubstrate.lean` | StandardModel substrate = odd naturals | `standardModel_image_iff_odd`, `standardModel_naming_gap` |
| `WTS/ReturnPath/RedIsSubstrate.lean` | Chain-specific red as substrate | `red_idempotent`, `invariantSubstrate_of_red` |
| `WTS/ReturnPath/PartialReturn.lean` | Subdomain return for Group B | `partialLambek_zero_gap`, `partial_bridge_via_gradeGap` |
| `WTS/ReturnPath/Generator.lean` | Profile collapse + axiom strata | `tower_complete`, `classification_dn`, `four_strata`, `polymarkov_peqnp` |

**Naming/ files (`WTS/ReturnPath/Naming/`):**

| File | Role | Key results |
|---|---|---|
| `Naming/GradeGapMeasure.lean` | gradeGap ruler | `compatible_iff_nonpositive_gap`, `gap_trichotomy` |
| `Naming/OmegaGradeTransfer.lean` | omega grade overhead | `gradeGap_determines_factoring`, `gradeGap_determines_regime` |
| `Naming/ReturnPathAtPositions.lean` | transport model grade | `transport_model_zero_gap`, `universal_grade_contrast` |
| `Naming/CountingBoundary.lean` | growth gap boundary | `gradeGap_anti_compression_assembly`, `standardModel_separation_complete` |
| `Naming/DeficitEquivalence.lean` | Nat decomposition | `nonpositive_gap_iff_zero_deficit`, `deficit_trichotomy` |
| `Naming/SeparationLocalization.lean` | separation localization | `separation_fully_localized`, `separation_requirements` |
| `Naming/NamingAccess.lean` | naming's access to substrate | `naming_access_characterization`, `separation_is_naming_failure` |
| `Naming/ReflexiveToGraded.lean` | Reflexive-to-graded derivation | `fullReflexive_selfApp_eq_id`, `grounding_summary` |
| *(5 files archived to archive/naming-supplementary/)* | | |
| `WTS/ReturnPath/SeparationLocalization.lean` | Separation localized to positive-gap region | `separation_fully_localized`, `separation_localized_to_positive_gap` |
| `WTS/ReturnPath/WeakReflData.lean` | Computation/naming boundary: retraction suffices for computation | `WeakReflData`, `weak_omega_fixed_point` |

ReturnPath axiom profile: **none** (ConstructiveOmega); propext + Quot.sound (all others). No Classical.choice. No Mathlib. No custom axioms.

### Transport + Core (assembled from pnp-integrated) — 11 files

| File | Role | Key results |
|---|---|---|
| `WTS/Core.lean` | Foundation: GRM, models, conservativity | `conservativity`, `selfApp_not_factors` |
| `WTS/Transport/WitnessTransportCore.lean` | Transport primitives | `consequence_closed_compose_pair` |
| `WTS/Transport/ConsequenceClosureCore.lean` | Chain composition | `consequence_closed_compose` |
| `WTS/Transport/TransportSelfSimilarity.lean` | Self-similarity, structural retraction | `transport_model_selfApp_eq_id`, `structural_retraction` |
| `WTS/Transport/TransportCollapseObstruction.lean` | Collapse obstruction | `sideA_bounded_selector_impossible` (proved) |
| `WTS/Transport/AggregationDepthBarrier.lean` | Aggregation overhead | `overhead_constitutivity`, `no_static_certificate_replacement` |
| `WTS/Transport/BindingStructure.lean` | Consequence binding | `consequence_binding_bound`, `coherent_field_non_decomposable` |
| `WTS/Transport/ProjectionPreservation.lean` | Projection structure | `projection_grade_stable` |
| `WTS/Transport/BridgeNecessity.lean` | Bridge necessity | `measure_bridge_compatible_with_both_regimes` |
| `WTS/Transport/OmegaChainCompletion.lean` | Omega-chain, Lambek data | `bridge_factory`, `lambek_factory` |
| `WTS/Transport/ObstructionInvariance.lean` | Pushforward/pullback | `partial_bridge_invariant` |

### Shared + Protocol (assembled from classical-constraints) — 12 files

| File | Role | Key results |
|---|---|---|
| `WTS/Shared/Basic.lean` | InstanceFamily definitions | `InstanceFamily` |
| `WTS/Shared/SATPresheafCore.lean` | SAT instances, gluing | `gluing_iff_satisfiable` |
| `WTS/Shared/CookSelectorBridge.lean` | Bounded selector bridge | `poly_solver_induces_bounded_selector`, `capacity_gap_implies_blind_spots` |
| `WTS/Shared/CookFaithfulness.lean` | Cook encoding, faithfulness | `CookEncoding`, `CookFaithful` (open) |
| `WTS/Shared/SideAMirror.lean` | Mirror types + axiom | 35 declarations (9 structures, 7 defs, 1 axiom, 18 theorems), `selfApp_nonincreasing_contradiction` |
| `WTS/Protocol/DistributedWitnessCore.lean` | Distributed witness system | `DistributedWitnessSystem`, `WitnessSovereignty` |
| `WTS/Protocol/CapabilityWitnessInstance.lean` | Capability witness | `capabilityWitnessSystem`, collapse properties |
| `WTS/Protocol/ConsensusWitnessInstance.lean` | Consensus witness | `consensusWitnessSystem` (parameterized) |
| `WTS/Protocol/ZKProjectionInstance.lean` | ZK witness | `zkWitnessSystem` (parameterized) |
| `WTS/Protocol/CoherenceTransportMeasure.lean` | Coherence measure | `coherence_max_implies_closed` (parameterized) |
| `WTS/Protocol/ValueCollapseInstance.lean` | Value collapse | `price_is_projection` (parameterized) |
| `WTS/Protocol/ProtocolWitnessFamilyLock.lean` | Lock theorem | `no_bounded_protocol_shortcuts` (conditional) |
| `WTS/Protocol/ProtocolGRMBridge.lean` | DWS-to-GRM bridge | `coherence_gradeGap_bridge`, `ProtocolGRM.cotrip_groupC` |

### Totals

- **70 files**, 0 sorry
- **Tower**: 21 files, ~285 theorems (carrier architecture: ~205 across 9 files; core structures/forward implications axiom-free, iff-theorems use propext + Quot.sound, Classical.choice for witness extraction); propext + Quot.sound for older tower files
- **ReturnPath**: 25 files, ~170 theorems, none (ConstructiveOmega/trivialModel_compatible_complete) or propext + Quot.sound
- **Foundation + Transport**: 11 files, ~170 declarations, propext + Quot.sound
- **Shared + Protocol**: 13 files, ~180 declarations, adds 1 custom axiom
- **Custom axioms**: 1 (`sideA_bounded_selector_impossible_mirror`)
- **Standard axioms**: propext, Quot.sound (most files); genuinely axiom-free: ConstructiveOmega, and carrier architecture core structures/forward implications (ReflectiveCarrierData, SplitIdempotent, UniversalProperty, AdmissibleBridge, DynamicDriftCarrier definition); carrier architecture iff-theorems use propext + Quot.sound; Classical.choice enters for biconditionals requiring witness extraction (unbounded_gap_iff_no_finite_drift, exists_least_drift, actualDriftFn/leastDriftAt via Nat.find) and reverse directions of FiniteDrift/UnboundedGap equivalences
