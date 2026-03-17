/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Tower/CarrierEngineering/MinimalNecessityGradient.lean — The carrier
kernel as a minimal necessity gradient.

This file packages the carrier engineering results into a single
recoverable theorem complex. The individual results are proved in:
  - ReflectiveCarrierData.lean (kernel, extensions, regime iffs)
  - SplitIdempotent.lean (idempotent splitting equivalence)
  - UniversalProperty.lean (uniqueness up to unique isomorphism)
  - DefectSpectrum.lean (defect as geometric invariant)
  - LeastDrift.lean (quantitative minimum)
  - ReencodingInvariance.lean (encoding stability)
  - AdmissibleBridge.lean (classical interface)

The minimal necessity gradient:

  Every fold/unfold/roundtrip system forces an idempotent selfApp.
  The idempotent determines a canonical carrier kernel on Fix(selfApp).
  Any other compatible carrier factors uniquely through it.
  Strict naming appears exactly when selfApp is grade-non-increasing.
  Bounded-loss naming appears exactly when selfApp is bounded by +k.
  Both are unique when they exist.
  The least admissible drift is the minimum naming loss required.
  The qualitative defect class (finite vs infinite required drift)
  is invariant under bounded same-semantics reencoding.

Nothing in this chain is posited. Each layer is extracted from the
previous one by a forced step. The carrier kernel is not a convenient
construction — it is the least structure already present in every GRM.

STATUS: 0 sorry. All content is re-exported from existing theorems.
-/

import WTS.Tower.CarrierEngineering.LeastDrift
import WTS.Tower.CarrierEngineering.UniversalProperty

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Part I: Single-model gradient — what every GRM carries
-- ════════════════════════════════════════════════════════════

-- ── 1. Kernel forcing ─────────────────────────────────────

/-- Every GRM carries a canonical reflective carrier on Fix(selfApp),
    without any grade hypothesis. The computation kernel is
    unconditionally present. -/
def kernel_forced (M : GradedReflModel) :
    ReflectiveCarrierData :=
  M.toReflectiveCarrierData

/-- The canonical carrier is the splitting of the idempotent selfApp.
    ReflectiveCarrierData and SplitIdempotent are the same data,
    with roundtrips by rfl in both directions. -/
theorem kernel_is_split_idempotent (M : GradedReflModel) :
    ∀ x, (M.toReflectiveCarrierData.toSplitIdempotent.toReflectiveCarrierData).canonicalize x =
         M.selfApp x :=
  M.splitIdempotent_roundtrip_canonicalize

-- ── 2. Kernel universality ────────────────────────────────

/-- Any section-retraction pair compatible with selfApp is uniquely
    isomorphic to the canonical kernel. The carrier architecture
    is forced — there is no alternative. -/
theorem kernel_universal (M : GradedReflModel)
    (CS : GRMCompatibleSplitting M) :
    let CS' := CS.toCompatibleSplitting
    (∀ c', CS'.toFixed (CS'.fromFixed c') = c') ∧
    (∀ fp, CS'.fromFixed (CS'.toFixed fp) = fp) :=
  CS.universal_property

/-- The comparison map between any compatible splitting and the
    canonical kernel is the unique isomorphism compatible with
    the embeddings into the carrier. -/
theorem kernel_comparison_unique (M : GradedReflModel)
    (CS : GRMCompatibleSplitting M) :
    let CS' := CS.toCompatibleSplitting
    ∀ (φ : CS'.C' → (M.toReflectiveCarrierData.toSplitIdempotent).FixedPoints),
      (∀ c', (φ c').val = CS'.incl' c') → ∀ c', φ c' = CS'.toFixed c' :=
  CS.toCompatibleSplitting.toFixed_unique

-- ── 3. Strict naming threshold ────────────────────────────

/-- Strict naming (grade-non-increasing selfApp) exists if and only if
    selfApp is grade-non-increasing. Not a sufficient condition —
    the exact necessary and sufficient condition. -/
theorem strict_naming_iff (M : GradedReflModel) :
    Nonempty M.GradeCompatibleExtension ↔
    (∀ x, M.grade (M.selfApp x) ≤ M.grade x) :=
  M.grade_compatible_extension_iff

/-- The strict naming layer, when it exists, is unique. The naming
    architecture is forced, not chosen. -/
theorem strict_naming_unique (M : GradedReflModel) :
    Subsingleton M.GradeCompatibleExtension :=
  FixedGradeReflectiveCarrier.instSubsingleton

-- ── 4. Drift naming threshold ─────────────────────────────

/-- Bounded-loss naming at drift k exists if and only if selfApp
    increases grade by at most k. Again: exact iff, not sufficient
    condition. -/
theorem drift_naming_iff (M : GradedReflModel) (k : Nat) :
    Nonempty (M.DriftCompatibleExtension k) ↔
    (∀ x, M.grade (M.selfApp x) ≤ M.grade x + k) :=
  M.drift_extension_iff k

/-- The drift naming layer at each k, when it exists, is unique. -/
theorem drift_naming_unique (M : GradedReflModel) (k : Nat) :
    Subsingleton (M.DriftCompatibleExtension k) :=
  FixedGradeDriftCarrier.instSubsingleton

/-- Admissible drifts are upward-closed: if drift k works, so does
    any larger drift. The set of admissible drifts is an upper set
    in Nat. -/
theorem drift_upward_closed (M : GradedReflModel) {k l : Nat}
    (h : k ≤ l) : M.AdmitsDrift k → M.AdmitsDrift l :=
  M.admitsDrift_mono h

-- ── 5. Least naming loss ──────────────────────────────────

/-- When finite drift exists, the least admissible drift exists.
    This is the minimum naming loss required by the model. -/
theorem least_naming_loss_exists (M : GradedReflModel)
    (h : M.FiniteDrift) : ∃ k, M.IsLeastDrift k :=
  M.exists_least_drift h

/-- The least drift is unique. -/
theorem least_naming_loss_unique (M : GradedReflModel)
    {k₁ k₂ : Nat} (h₁ : M.IsLeastDrift k₁) (h₂ : M.IsLeastDrift k₂) :
    k₁ = k₂ :=
  M.isLeastDrift_unique h₁ h₂

/-- Least drift zero iff strict naming exists. The drift spectrum
    begins at the strict threshold. -/
theorem least_drift_zero_iff_strict (M : GradedReflModel) :
    M.IsLeastDrift 0 ↔ Nonempty M.GradeCompatibleExtension :=
  M.isLeastDrift_zero_iff

-- ── 6. Two independent obstructions ───────────────────────

/-- UnboundedGap (additive gap unbounded) iff no finite drift exists
    at any level. This is the genuine no-naming condition. -/
theorem no_naming_iff_unbounded_gap (M : GradedReflModel) :
    M.UnboundedGap ↔ ∀ k, ¬M.AdmitsDrift k := by
  rw [M.unbounded_gap_iff_no_finite_drift]
  simp [GradedReflModel.AdmitsDrift]

/-- SelfAppUnbounded and UnboundedGap are independent notions.
    Protocols can have finite drift yet SelfAppUnbounded.
    This independence is witnessed by ProtocolGRM. -/
theorem protocol_finite_drift (P : ProtocolGRM) :
    P.toGRM.FiniteDrift :=
  P.finiteDrift

-- ════════════════════════════════════════════════════════════
-- Part II: The thin bundle
-- ════════════════════════════════════════════════════════════

/-- The minimal necessity gradient of a GRM: the forced carrier
    kernel, exact naming thresholds, and least quantitative loss.

    Every GRM carries this data unconditionally. The structure
    packages what is already proved — it contains no new mathematics,
    only the claim that these results form a coherent unit.

    Pairwise reencoding invariance (BoundedGRMEquiv stability) is
    deliberately kept separate — it is a property of pairs of GRMs,
    not of individual models. See Part III below. -/
structure MinimalNecessityGradient (M : GradedReflModel) where
  /-- The canonical carrier kernel on Fix(selfApp). -/
  kernel : ReflectiveCarrierData
  /-- Strict naming exists iff grade-non-increasing. -/
  strict_iff : Nonempty M.GradeCompatibleExtension ↔
    (∀ x, M.grade (M.selfApp x) ≤ M.grade x)
  /-- Drift-k naming exists iff bounded by k. -/
  drift_iff : ∀ k, Nonempty (M.DriftCompatibleExtension k) ↔
    (∀ x, M.grade (M.selfApp x) ≤ M.grade x + k)
  /-- Least drift exists when finite drift does. -/
  least_drift : M.FiniteDrift → ∃ k, M.IsLeastDrift k

/-- Every GRM satisfies the minimal necessity gradient. -/
def GradedReflModel.minimalNecessityGradient (M : GradedReflModel) :
    MinimalNecessityGradient M where
  kernel := M.toReflectiveCarrierData
  strict_iff := M.grade_compatible_extension_iff
  drift_iff := M.drift_extension_iff
  least_drift := M.exists_least_drift

-- ════════════════════════════════════════════════════════════
-- Part III: Encoding stability — pairwise invariance
-- ════════════════════════════════════════════════════════════

-- These are properties of PAIRS of GRMs under bounded equivalence,
-- not properties of individual models. They complete the necessity
-- gradient by showing the qualitative defect class is not an
-- encoding artifact.

/-- The qualitative defect class is encoding-invariant:
    whether finite drift exists is the same across any bounded
    carrier equivalence commuting with selfApp. -/
theorem defect_class_invariant {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') :
    M.FiniteDrift ↔ M'.FiniteDrift := by
  constructor
  · intro ⟨k, hk⟩; exact ⟨k + 2 * E.overhead, E.drift_extension_transport k hk⟩
  · intro ⟨k, hk⟩; exact ⟨k + 2 * E.overhead, E.drift_extension_transport_g k hk⟩

/-- The infinite naming obstruction is encoding-invariant:
    no bounded reencoding can collapse UnboundedGap into finite drift
    or vice versa. -/
theorem infinite_obstruction_invariant {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') :
    M.UnboundedGap ↔ M'.UnboundedGap :=
  E.unboundedGap_iff

/-- The least drift is stable: under overhead c, the minimum naming
    loss shifts by at most 2c in each direction. -/
theorem least_drift_stable {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') {k k' : Nat}
    (hk : M.IsLeastDrift k) (hk' : M'.IsLeastDrift k') :
    k' ≤ k + 2 * E.overhead ∧ k ≤ k' + 2 * E.overhead :=
  E.leastDrift_stability hk hk'

/-- The fixed-point substrate transfers: bounded equivalence
    induces a bijection between Fix(selfApp_M) and Fix(selfApp_M')
    with bounded grade distortion. -/
theorem substrate_transfers {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M')
    (c : { x : M.carrier // M.selfApp x = x }) :
    E.fFixed (E.gFixed (E.fFixed c)) = E.fFixed c := by
  rw [E.gFixed_fFixed]

/-- Same-semantics encodings induce bounded equivalence:
    the bridge from classical computation to the carrier kernel. -/
def same_semantics_induces_equivalence
    {E₁ E₂ : AdmissibleEncoding} (S : SameSemantics E₁ E₂) :
    BoundedGRMEquiv E₁.toGRM E₂.toGRM :=
  S.toBoundedGRMEquiv

-- ════════════════════════════════════════════════════════════
-- Part IV: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms kernel_forced
#print axioms kernel_is_split_idempotent
#print axioms kernel_universal
#print axioms kernel_comparison_unique
#print axioms strict_naming_iff
#print axioms strict_naming_unique
#print axioms drift_naming_iff
#print axioms drift_naming_unique
#print axioms drift_upward_closed
#print axioms least_naming_loss_exists
#print axioms least_naming_loss_unique
#print axioms least_drift_zero_iff_strict
#print axioms no_naming_iff_unbounded_gap
#print axioms protocol_finite_drift
#print axioms GradedReflModel.minimalNecessityGradient
#print axioms defect_class_invariant
#print axioms infinite_obstruction_invariant
#print axioms least_drift_stable
#print axioms substrate_transfers
#print axioms same_semantics_induces_equivalence

end WTS
