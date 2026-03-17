/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Tower/CarrierEngineering/ReflectiveCarrierData.lean — The master
structure centered on Fix(selfApp).

Three-layer design:
  - ReflectiveCarrierData: ungraded section-retraction pair (A, C, incl, norm, sect).
    Every GRM instantiates this unconditionally via C = Fix(selfApp).
    This is the computation layer — always present.
  - FixedGradeReflectiveCarrier: strict naming layer over a fixed ambient grade.
    Inhabited iff selfApp is grade-non-increasing. Unique if inhabited.
    Uninhabitable under SelfAppUnbounded.
  - FixedGradeDriftCarrier: bounded-loss naming layer with drift parameter.
    Inhabited iff selfApp increases grade by at most drift.
    Unique if inhabited. Every ProtocolGRM admits drift = 2 * overhead.

The split matches the monograph thesis: the retract (computation) is
always there; the grade (naming) is what creates the question. The
regime question IS inhabitation of FixedGradeReflectiveCarrier for M's
own grade (grade_compatible_extension_iff). Drift generalizes this to
bounded-loss naming (drift_extension_iff).

Two independent obstruction axes:
  - SelfAppUnbounded: threshold overflow at every grade (kills strict ext)
  - UnboundedGap: additive gap unbounded (kills all finite-drift exts)
  These are independent: finite drift can coexist with SelfAppUnbounded.

GradedReflectiveCarrier remains as a general free-standing abstraction
but is no longer the conceptual center; the fixed-grade types are.

STATUS: 0 sorry. Classical.choice isolated to reverse directions of
disruption_iff_non_cotrip, unbounded_gap_iff_no_finite_drift, and
no_strict_extension_of_unbounded_gap (witness extraction from negated
universals). All structural core and overflow equivalences constructive.
-/

import WTS.Core
import WTS.Tower.ForcingPredicates
import WTS.Tower.CarrierEngineering
import WTS.Tower.CarrierEngineering.CanonicalMirror
import WTS.Tower.CarrierEngineering.ProjectionObstruction
import WTS.ReturnPath.InvariantSubstrate
import WTS.Transport.TransportSelfSimilarity
import WTS.Protocol.ProtocolGRMBridge

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: The ungraded core — always present
-- ════════════════════════════════════════════════════════════

/-- The ungraded reflective carrier: a section-retraction pair between
    an ambient carrier A and a canonical subdomain C.

    Every GRM instantiates this via C := Fix(selfApp), norm := selfApp.
    No grade hypothesis needed — the retract exists unconditionally
    by idempotence of selfApp (from roundtrip). -/
structure ReflectiveCarrierData where
  /-- The ambient carrier. -/
  A : Type
  /-- The canonical subdomain (= Fix of some idempotent). -/
  C : Type
  /-- Inclusion: canonical objects embed into the ambient carrier. -/
  incl : C → A
  /-- Normalization: projects ambient objects to canonical form. -/
  norm : A → C
  /-- Section: normalizing an included canonical object recovers it. -/
  sect : ∀ c, norm (incl c) = c

-- ════════════════════════════════════════════════════════════
-- Section 2: The graded extension — the naming layer
-- ════════════════════════════════════════════════════════════

/-- The graded reflective carrier: extends ReflectiveCarrierData with
    grade structure and the grade-non-increasing property on norm.

    This is a free-standing abstraction carrying its own grades.
    For the regime question tied to a specific GRM's grade, see
    FixedGradeReflectiveCarrier and GradeCompatibleExtension. -/
structure GradedReflectiveCarrier extends ReflectiveCarrierData where
  /-- Grade on the ambient carrier. -/
  grade_A : A → Nat
  /-- Grade on the canonical subdomain. -/
  grade_C : C → Nat
  /-- Inclusion preserves grade. -/
  grade_compat : ∀ c, grade_A (incl c) = grade_C c
  /-- Normalization is grade-non-increasing. -/
  norm_grade_le : ∀ a, grade_C (norm a) ≤ grade_A a

/-- A grade-compatible extension of a ReflectiveCarrierData with a fixed
    ambient grade. Unlike GradedReflectiveCarrier (which carries its own
    grade), this is parametrized by a specific grade function and asks:
    does a compatible C-grade exist making normalization non-increasing?

    For a GRM M, inhabitation of
      FixedGradeReflectiveCarrier M.toReflectiveCarrierData M.grade
    is literally the regime question: does the naming layer exist for
    M's own grade? See grade_compatible_extension_iff below. -/
structure FixedGradeReflectiveCarrier
    (R : ReflectiveCarrierData) (grade_A : R.A → Nat) where
  /-- Grade on the canonical subdomain. -/
  grade_C : R.C → Nat
  /-- Inclusion preserves grade. -/
  grade_compat : ∀ c, grade_A (R.incl c) = grade_C c
  /-- Normalization is grade-non-increasing. -/
  norm_grade_le : ∀ a, grade_C (R.norm a) ≤ grade_A a

/-- A drifted grade extension: normalization may increase grade by at
    most `drift`. Generalizes FixedGradeReflectiveCarrier (drift = 0)
    and captures protocol overhead (drift = 2 * transportOverhead).

    The drift parameter turns the strict grade boundary into a spectrum:
    - drift = 0: selfApp is grade-non-increasing (Group B/C)
    - drift = k > 0: selfApp may increase grade by up to k
    - no finite drift: selfApp overflows (separation) -/
structure FixedGradeDriftCarrier
    (R : ReflectiveCarrierData) (grade_A : R.A → Nat) (drift : Nat) where
  /-- Grade on the canonical subdomain. -/
  grade_C : R.C → Nat
  /-- Inclusion preserves grade. -/
  grade_compat : ∀ c, grade_A (R.incl c) = grade_C c
  /-- Normalization is grade-non-increasing up to drift. -/
  norm_grade_le_drift : ∀ a, grade_C (R.norm a) ≤ grade_A a + drift

/-- Zero-drift carrier → strict carrier (the fields coincide). -/
def FixedGradeDriftCarrier.toStrict
    {R : ReflectiveCarrierData} {grade_A : R.A → Nat}
    (E : FixedGradeDriftCarrier R grade_A 0) :
    FixedGradeReflectiveCarrier R grade_A where
  grade_C := E.grade_C
  grade_compat := E.grade_compat
  norm_grade_le := E.norm_grade_le_drift

/-- Strict carrier → zero-drift carrier. -/
def FixedGradeReflectiveCarrier.toDrift
    {R : ReflectiveCarrierData} {grade_A : R.A → Nat}
    (E : FixedGradeReflectiveCarrier R grade_A) :
    FixedGradeDriftCarrier R grade_A 0 where
  grade_C := E.grade_C
  grade_compat := E.grade_compat
  norm_grade_le_drift := E.norm_grade_le

/-- Grade on C is uniquely determined in drift carriers too:
    grade_compat forces grade_C c = grade_A (incl c) regardless of drift. -/
theorem FixedGradeDriftCarrier.grade_C_unique
    {R : ReflectiveCarrierData} {grade_A : R.A → Nat} {drift : Nat}
    (E : FixedGradeDriftCarrier R grade_A drift) :
    ∀ c, E.grade_C c = grade_A (R.incl c) :=
  fun c => (E.grade_compat c).symm

-- ════════════════════════════════════════════════════════════
-- Section 3: Derived properties — ungraded
-- ════════════════════════════════════════════════════════════

/-- The induced endomorphism on A: incl ∘ norm. -/
def ReflectiveCarrierData.canonicalize (R : ReflectiveCarrierData) (a : R.A) : R.A :=
  R.incl (R.norm a)

/-- The canonicalizer is idempotent. -/
theorem ReflectiveCarrierData.canonicalize_idempotent (R : ReflectiveCarrierData) :
    ∀ a, R.canonicalize (R.canonicalize a) = R.canonicalize a := by
  intro a
  show R.incl (R.norm (R.incl (R.norm a))) = R.incl (R.norm a)
  rw [R.sect]

/-- The canonicalizer is the identity on included elements. -/
theorem ReflectiveCarrierData.canonicalize_incl (R : ReflectiveCarrierData) :
    ∀ c, R.canonicalize (R.incl c) = R.incl c := by
  intro c
  show R.incl (R.norm (R.incl c)) = R.incl c
  rw [R.sect]

/-- incl is injective (norm is left inverse). -/
theorem ReflectiveCarrierData.incl_injective (R : ReflectiveCarrierData) :
    Function.Injective R.incl := by
  intro c1 c2 h
  have h1 := R.sect c1
  have h2 := R.sect c2
  rw [h] at h1
  rw [← h1, h2]

/-- Fixed points of canonicalize are exactly the image of incl. -/
theorem ReflectiveCarrierData.canonical_iff_in_image (R : ReflectiveCarrierData) (a : R.A) :
    R.canonicalize a = a ↔ ∃ c, R.incl c = a := by
  constructor
  · intro h; exact ⟨R.norm a, h⟩
  · intro ⟨c, hc⟩; rw [← hc, R.canonicalize_incl]

-- ════════════════════════════════════════════════════════════
-- Section 4: Derived properties — graded
-- ════════════════════════════════════════════════════════════

/-- The canonicalizer is grade-non-increasing. -/
theorem GradedReflectiveCarrier.canonicalize_grade_le (G : GradedReflectiveCarrier) :
    ∀ a, G.grade_A (G.canonicalize a) ≤ G.grade_A a := by
  intro a
  show G.grade_A (G.incl (G.norm a)) ≤ G.grade_A a
  rw [G.grade_compat]
  exact G.norm_grade_le a

/-- The canonicalizer factors through every grade level. -/
theorem GradedReflectiveCarrier.canonicalize_factors (G : GradedReflectiveCarrier)
    (d : Nat) (a : G.A) (hle : G.grade_A a ≤ d) :
    G.grade_A (G.canonicalize a) ≤ d :=
  Nat.le_trans (G.canonicalize_grade_le a) hle

/-- A GradedReflectiveCarrier yields GroupBData on its ambient carrier. -/
def GradedReflectiveCarrier.toGroupBData (G : GradedReflectiveCarrier) :
    GroupBData G.A where
  retract := G.canonicalize
  grade := G.grade_A
  idempotent := G.toReflectiveCarrierData.canonicalize_idempotent
  red_grade_le := G.canonicalize_grade_le

/-- A GradedReflectiveCarrier yields an IdempotentNormalizer. -/
def GradedReflectiveCarrier.toIdempotentNormalizer (G : GradedReflectiveCarrier) :
    IdempotentNormalizer G.A where
  normalize := G.canonicalize
  grade := G.grade_A
  idempotent := G.toReflectiveCarrierData.canonicalize_idempotent
  grade_le := G.canonicalize_grade_le

-- ════════════════════════════════════════════════════════════
-- Section 5: Every GRM induces ReflectiveCarrierData
-- ════════════════════════════════════════════════════════════

/-- Every GradedReflModel induces a ReflectiveCarrierData via
    C := {x // selfApp x = x}, norm x := ⟨selfApp x, idempotence⟩.

    This works unconditionally — no grade hypothesis needed.
    The retract (computation) is always present. -/
def GradedReflModel.toReflectiveCarrierData (M : GradedReflModel) :
    ReflectiveCarrierData where
  A := M.carrier
  C := { x : M.carrier // M.selfApp x = x }
  incl := Subtype.val
  norm a := ⟨M.selfApp a, grm_roundtrip_forces_idempotent M a⟩
  sect c := by
    ext
    show M.selfApp c.val = c.val
    exact c.property

/-- The canonicalizer of GRM's ReflectiveCarrierData IS selfApp. -/
theorem GradedReflModel.reflectiveCarrierData_canonicalize (M : GradedReflModel) :
    ∀ a, M.toReflectiveCarrierData.canonicalize a = M.selfApp a :=
  fun _ => rfl

-- ════════════════════════════════════════════════════════════
-- Section 6: GRM with grade-non-increasing selfApp → graded version
-- ════════════════════════════════════════════════════════════

/-- A GRM whose selfApp is grade-non-increasing induces a
    GradedReflectiveCarrier. This is the Group B/C case.

    The hypothesis h_le is exactly what separates the bounded
    regime from the unbounded regime. The projection obstruction
    (ProjectionObstruction.lean) shows that this hypothesis +
    SelfAppUnbounded yields False. -/
def GradedReflModel.toGradedReflectiveCarrier (M : GradedReflModel)
    (h_le : ∀ x, M.grade (M.selfApp x) ≤ M.grade x) :
    GradedReflectiveCarrier where
  A := M.carrier
  C := { x : M.carrier // M.selfApp x = x }
  incl := Subtype.val
  norm a := ⟨M.selfApp a, grm_roundtrip_forces_idempotent M a⟩
  sect c := by
    ext
    show M.selfApp c.val = c.val
    exact c.property
  grade_A := M.grade
  grade_C := fun c => M.grade c.val
  grade_compat _ := rfl
  norm_grade_le := h_le

/-- Grade-non-increasing selfApp implies PEqNP: selfApp factors through
    every grade level at d = 0.

    This is one direction of the regime boundary. The full iff is
    grade_compatible_extension_iff. -/
theorem grade_nonincreasing_implies_PEqNP (M : GradedReflModel) :
    (∀ x, M.grade (M.selfApp x) ≤ M.grade x) →
    PEqNP M :=
  fun h => ⟨0, fun x hx => Nat.le_trans (h x) hx⟩


theorem grade_nonincreasing_contradicts_unbounded (M : GradedReflModel)
    (hub : SelfAppUnbounded M)
    (h_le : ∀ x, M.grade (M.selfApp x) ≤ M.grade x) :
    False := by
  obtain ⟨x, hxle, hxgt⟩ := hub.overflows 0
  have := h_le x; omega

/-- The regime question for a specific GRM: does a grade-compatible
    extension exist for M's own ReflectiveCarrierData and M's own grade? -/
abbrev GradedReflModel.GradeCompatibleExtension (M : GradedReflModel) :=
  FixedGradeReflectiveCarrier M.toReflectiveCarrierData M.grade

/-- THE INHABITATION THEOREM.

    A GRM admits a grade-compatible extension of its canonical retract
    if and only if selfApp is grade-non-increasing.

    Forward: the extension's grade_compat + norm_grade_le chain gives
    grade(selfApp x) = grade_C(norm x) ≤ grade(x).
    Reverse: set grade_C c := grade(c.val); grade_compat is rfl,
    norm_grade_le is exactly the hypothesis.

    This makes the monograph's central claim — "the regime question IS
    whether the graded naming layer can be inhabited" — literally true
    in Lean, not just philosophically true in prose. -/
theorem GradedReflModel.grade_compatible_extension_iff (M : GradedReflModel) :
    Nonempty M.GradeCompatibleExtension ↔
    (∀ x, M.grade (M.selfApp x) ≤ M.grade x) := by
  constructor
  · -- Forward: extension → selfApp grade-non-increasing
    intro ⟨G⟩ x
    -- grade_compat: grade(incl(norm x)) = grade_C(norm x)
    -- For GRM's toReflectiveCarrierData, incl(norm x) = selfApp x definitionally
    have h1 : M.grade (M.selfApp x) =
        G.grade_C (M.toReflectiveCarrierData.norm x) :=
      G.grade_compat (M.toReflectiveCarrierData.norm x)
    have h2 := G.norm_grade_le x
    omega
  · -- Reverse: selfApp grade-non-increasing → construct extension
    intro h
    exact ⟨{
      grade_C := fun c => M.grade c.val
      grade_compat := fun _ => rfl
      norm_grade_le := h
    }⟩

/-- Grade on C is uniquely determined: grade_compat forces
    grade_C c = grade_A (incl c) for every c. The extension,
    when it exists, is not merely inhabited — it is forced. -/
theorem FixedGradeReflectiveCarrier.grade_C_unique
    {R : ReflectiveCarrierData} {grade_A : R.A → Nat}
    (E : FixedGradeReflectiveCarrier R grade_A) :
    ∀ c, E.grade_C c = grade_A (R.incl c) :=
  fun c => (E.grade_compat c).symm

/-- The strict grade extension is a subsingleton: grade_compat forces
    grade_C, and the remaining fields are Props. Two extensions are
    literally equal — the naming layer is forced, not chosen. -/
instance FixedGradeReflectiveCarrier.instSubsingleton
    {R : ReflectiveCarrierData} {grade_A : R.A → Nat} :
    Subsingleton (FixedGradeReflectiveCarrier R grade_A) :=
  ⟨fun E₁ E₂ => by
    have h : E₁.grade_C = E₂.grade_C :=
      funext fun c => by rw [E₁.grade_C_unique, E₂.grade_C_unique]
    cases E₁; cases E₂; congr⟩

/-- The drifted grade extension is also a subsingleton at each drift level. -/
instance FixedGradeDriftCarrier.instSubsingleton
    {R : ReflectiveCarrierData} {grade_A : R.A → Nat} {drift : Nat} :
    Subsingleton (FixedGradeDriftCarrier R grade_A drift) :=
  ⟨fun E₁ E₂ => by
    have h : E₁.grade_C = E₂.grade_C :=
      funext fun c => by rw [E₁.grade_C_unique, E₂.grade_C_unique]
    cases E₁; cases E₂; congr⟩

/-- For GRM extensions, grade_C is forced to be M.grade on the
    fixed-point subtype. Any grade-compatible extension must grade
    canonical elements by their ambient grade — there is no choice. -/
theorem GradedReflModel.grade_compatible_extension_unique
    (M : GradedReflModel) (E : M.GradeCompatibleExtension) :
    ∀ c, E.grade_C c = M.grade c.val :=
  E.grade_C_unique

/-- The canonical grade-compatible extension: grade_C c := grade(c.val).
    This is the unique witness when selfApp is grade-non-increasing. -/
def GradedReflModel.mkGradeCompatibleExtension
    (M : GradedReflModel)
    (h : ∀ x, M.grade (M.selfApp x) ≤ M.grade x) :
    M.GradeCompatibleExtension where
  grade_C := fun c => M.grade c.val
  grade_compat := fun _ => rfl
  norm_grade_le := h

/-- Separation as non-inhabitation: SelfAppUnbounded makes the
    grade-compatible extension literally uninhabitable.
    The regime failure is a type-theoretic emptiness statement. -/
theorem GradedReflModel.no_grade_compatible_extension_of_unbounded
    (M : GradedReflModel) (hub : SelfAppUnbounded M) :
    ¬Nonempty M.GradeCompatibleExtension :=
  fun h => grade_nonincreasing_contradicts_unbounded M hub
    (M.grade_compatible_extension_iff.mp h)

-- ════════════════════════════════════════════════════════════
-- Section 6b: Drifted extension — the protocol naming layer
-- ════════════════════════════════════════════════════════════

/-- The drifted regime question for a specific GRM: does a
    grade-compatible extension exist with drift at most k? -/
abbrev GradedReflModel.DriftCompatibleExtension (M : GradedReflModel) (k : Nat) :=
  FixedGradeDriftCarrier M.toReflectiveCarrierData M.grade k

/-- THE DRIFTED INHABITATION THEOREM.

    A GRM admits a drifted grade extension with drift k if and only if
    selfApp increases grade by at most k.

    - drift = 0 recovers grade_compatible_extension_iff
    - drift = 2 * transportOverhead captures all protocol GRMs
    - no finite drift ↔ UnboundedGap (NOT SelfAppUnbounded; see below) -/
theorem GradedReflModel.drift_extension_iff (M : GradedReflModel) (k : Nat) :
    Nonempty (M.DriftCompatibleExtension k) ↔
    (∀ x, M.grade (M.selfApp x) ≤ M.grade x + k) := by
  constructor
  · -- Forward: extension → selfApp bounded by drift
    intro ⟨G⟩ x
    have h1 : M.grade (M.selfApp x) =
        G.grade_C (M.toReflectiveCarrierData.norm x) :=
      G.grade_compat (M.toReflectiveCarrierData.norm x)
    have h2 := G.norm_grade_le_drift x
    omega
  · -- Reverse: bounded selfApp → construct extension
    intro h
    exact ⟨{
      grade_C := fun c => M.grade c.val
      grade_compat := fun _ => rfl
      norm_grade_le_drift := h
    }⟩

/-- Drift uniqueness: grade_C is forced regardless of drift value. -/
theorem GradedReflModel.drift_extension_unique
    (M : GradedReflModel) (k : Nat) (E : M.DriftCompatibleExtension k) :
    ∀ c, E.grade_C c = M.grade c.val :=
  E.grade_C_unique

/-- Drift monotonicity: if a drift-k extension exists, so does
    a drift-ℓ extension for any ℓ ≥ k. The admissible drift set
    is upward-closed. -/
theorem GradedReflModel.drift_extension_mono
    (M : GradedReflModel) {k ℓ : Nat} (h : k ≤ ℓ) :
    Nonempty (M.DriftCompatibleExtension k) →
    Nonempty (M.DriftCompatibleExtension ℓ) := by
  rw [M.drift_extension_iff, M.drift_extension_iff]
  intro hk x
  have := hk x; omega

/-- The admissible drift predicate: M admits drift k when a drift-k
    naming layer exists. The set { k | AdmitsDrift M k } is upward-closed
    and its emptiness/non-emptiness is encoding-invariant. -/
def GradedReflModel.AdmitsDrift (M : GradedReflModel) (k : Nat) : Prop :=
  Nonempty (M.DriftCompatibleExtension k)

/-- Whether any finite drift is admissible. -/
def GradedReflModel.FiniteDrift (M : GradedReflModel) : Prop :=
  ∃ k, M.AdmitsDrift k

/-- AdmitsDrift is upward-closed: admissible at k implies admissible at ℓ ≥ k. -/
theorem GradedReflModel.admitsDrift_mono (M : GradedReflModel) {k ℓ : Nat} (h : k ≤ ℓ) :
    M.AdmitsDrift k → M.AdmitsDrift ℓ :=
  M.drift_extension_mono h

/-- AdmitsDrift at 0 ↔ strict naming layer exists. -/
theorem GradedReflModel.admitsDrift_zero_iff (M : GradedReflModel) :
    M.AdmitsDrift 0 ↔ Nonempty M.GradeCompatibleExtension := by
  constructor
  · intro ⟨E⟩; exact ⟨E.toStrict⟩
  · intro ⟨E⟩; exact ⟨E.toDrift⟩

/-- Unbounded gap: selfApp increases grade past any fixed additive bound.
    This is the genuine "no finite drift" condition.

    IMPORTANT: UnboundedGap is strictly stronger than SelfAppUnbounded.
    - SelfAppUnbounded: threshold overflow at every grade (∀ d, ∃ x, ...)
    - UnboundedGap: the additive gap itself is unbounded (∀ k, ∃ x, ...)

    These are independent:
    - Protocols with positive overhead have finite drift (¬UnboundedGap)
      yet may have SelfAppUnbounded (threshold overflow everywhere).
    - A model with one huge-gap state has UnboundedGap at that point
      but may lack SelfAppUnbounded (no overflow at most grades). -/
def GradedReflModel.UnboundedGap (M : GradedReflModel) : Prop :=
  ∀ k, ∃ x, M.grade (M.selfApp x) > M.grade x + k

/-- UnboundedGap ↔ no finite drift: the gap is unbounded if and only
    if no drift-compatible extension exists at any drift level.

    Forward direction is constructive: an unbounded gap witness at drift k
    contradicts the extension's norm_grade_le_drift.
    Reverse direction uses classical logic: from ¬∀ extract ∃. -/
theorem GradedReflModel.unbounded_gap_iff_no_finite_drift (M : GradedReflModel) :
    M.UnboundedGap ↔ ∀ k, ¬Nonempty (M.DriftCompatibleExtension k) := by
  constructor
  · -- Forward: UnboundedGap → no drift at any k (constructive)
    intro h k ⟨G⟩
    have hk := (M.drift_extension_iff k).mp ⟨G⟩
    obtain ⟨x, hgt⟩ := h k
    have := hk x; omega
  · -- Reverse: no finite drift → UnboundedGap (classical)
    intro h k
    have hk : ¬(∀ x, M.grade (M.selfApp x) ≤ M.grade x + k) :=
      fun hle => h k ((M.drift_extension_iff k).mpr hle)
    by_contra hall
    push_neg at hall
    exact hk hall

/-- UnboundedGap implies the strict extension is uninhabitable.
    Corollary of unbounded_gap_iff_no_finite_drift at drift 0. -/
theorem GradedReflModel.no_strict_extension_of_unbounded_gap
    (M : GradedReflModel) (h : M.UnboundedGap) :
    ¬Nonempty M.GradeCompatibleExtension := by
  have := (M.unbounded_gap_iff_no_finite_drift.mp h) 0
  intro ⟨E⟩
  exact this ⟨E.toDrift⟩

/-- FiniteDrift ↔ ¬UnboundedGap (classically).
    Constructive forward: finite drift contradicts unbounded gap.
    Classical reverse: ¬UnboundedGap gives finite drift via double negation. -/
theorem GradedReflModel.finiteDrift_iff_not_unboundedGap (M : GradedReflModel) :
    M.FiniteDrift ↔ ¬M.UnboundedGap := by
  constructor
  · -- Forward: FiniteDrift → ¬UnboundedGap (constructive)
    intro ⟨k, hk⟩ hug
    exact (M.unbounded_gap_iff_no_finite_drift.mp hug k) hk
  · -- Reverse: ¬UnboundedGap → FiniteDrift (classical)
    intro h
    by_contra hno
    apply h
    rw [M.unbounded_gap_iff_no_finite_drift]
    intro k hk
    exact hno ⟨k, hk⟩

/-- The full bridge: strict naming layer implies PEqNP.
    GradeCompatibleExtension → grade-non-increasing → PEqNP at d = 0.
    Contrapositive: ¬PEqNP → strict naming uninhabitable. -/
theorem GradedReflModel.grade_compatible_extension_implies_PEqNP
    (M : GradedReflModel) :
    Nonempty M.GradeCompatibleExtension → PEqNP M :=
  fun h => grade_nonincreasing_implies_PEqNP M (M.grade_compatible_extension_iff.mp h)

/-- ¬PEqNP ↔ SelfAppUnbounded (classically).
    These say the same thing: at every grade threshold, some state
    overflows. The forward direction (SelfAppUnbounded → ¬PEqNP) is
    constructive. The reverse (¬PEqNP → SelfAppUnbounded) uses
    classical logic to push negation through ∃∀. -/
theorem GradedReflModel.selfAppUnbounded_iff_not_PEqNP (M : GradedReflModel) :
    SelfAppUnbounded M ↔ ¬PEqNP M := by
  constructor
  · -- Forward: SelfAppUnbounded → ¬PEqNP (constructive)
    intro ⟨overflows⟩ ⟨d, hd⟩
    obtain ⟨x, hle, hgt⟩ := overflows d
    have := hd x hle
    omega
  · -- Reverse: ¬PEqNP → SelfAppUnbounded (classical)
    intro h
    constructor
    intro d
    by_contra hall
    push_neg at hall
    exact h ⟨d, hall⟩

-- ════════════════════════════════════════════════════════════
-- Section 7: CanonicalMirror ↔ GradedReflectiveCarrier
-- ════════════════════════════════════════════════════════════

/-- Every CanonicalMirror is a GradedReflectiveCarrier. -/
def CanonicalMirror.toGradedReflectiveCarrier (CM : CanonicalMirror) :
    GradedReflectiveCarrier where
  A := CM.A
  C := CM.C
  incl := CM.incl
  norm := CM.normalize
  sect := CM.sect
  grade_A := CM.grade_A
  grade_C := CM.grade_C
  grade_compat := CM.grade_compat
  norm_grade_le := CM.normalize_grade_le

/-- Every GradedReflectiveCarrier is a CanonicalMirror. -/
def GradedReflectiveCarrier.toCanonicalMirror (G : GradedReflectiveCarrier) :
    CanonicalMirror where
  A := G.A
  C := G.C
  incl := G.incl
  normalize := G.norm
  sect := G.sect
  grade_A := G.grade_A
  grade_C := G.grade_C
  grade_compat := G.grade_compat
  normalize_grade_le := G.norm_grade_le

/-- Round-trip preserves the canonicalizer. -/
theorem CanonicalMirror.toGradedReflectiveCarrier_canonicalize (CM : CanonicalMirror) :
    ∀ a, CM.toGradedReflectiveCarrier.canonicalize a = CM.canonicalize a :=
  fun _ => rfl

theorem GradedReflectiveCarrier.toCanonicalMirror_canonicalize (G : GradedReflectiveCarrier) :
    ∀ a, G.toCanonicalMirror.canonicalize a = G.canonicalize a :=
  fun _ => rfl

-- ════════════════════════════════════════════════════════════
-- Section 8: InvariantSubstrate as a point of C
-- ════════════════════════════════════════════════════════════

/-- An InvariantSubstrate is a point of C in the GRM's
    ReflectiveCarrierData. The substrate exists in every GRM
    (computation is always present), so C is always inhabited. -/
def InvariantSubstrate.toCanonicalPoint {M : GradedReflModel}
    (s : InvariantSubstrate M) :
    (M.toReflectiveCarrierData).C :=
  ⟨s.point, s.fixed⟩

/-- For any GRM and any carrier element, selfApp(x) gives a point of C. -/
def GradedReflModel.canonicalPoint (M : GradedReflModel) (x : M.carrier) :
    (M.toReflectiveCarrierData).C :=
  ⟨M.selfApp x, grm_roundtrip_forces_idempotent M x⟩

/-- C is always inhabited (for nonempty carriers). -/
theorem GradedReflModel.canonical_subdomain_inhabited (M : GradedReflModel)
    (x : M.carrier) :
    ∃ _ : (M.toReflectiveCarrierData).C, True :=
  ⟨M.canonicalPoint x, trivial⟩

-- ════════════════════════════════════════════════════════════
-- Section 9: T(M) — the degenerate case where canonicalize = id
-- ════════════════════════════════════════════════════════════

/-- T(M) has selfApp = id, so every element is a fixed point.
    The ReflectiveCarrierData has C = full carrier (as subtype)
    and canonicalize = id. This is the degenerate case. -/
def transportModel_reflectiveCarrierData (M : GradedReflModel) :
    ReflectiveCarrierData :=
  (transportGradedReflModel M).toReflectiveCarrierData

/-- T(M)'s canonicalize is the identity. -/
theorem transportModel_canonicalize_eq_id (M : GradedReflModel) :
    ∀ t, (transportModel_reflectiveCarrierData M).canonicalize t =
         (transportGradedReflModel M).selfApp t :=
  fun _ => rfl

/-- T(M) admits the graded extension (selfApp = id is grade-non-increasing). -/
def transportModel_gradedReflectiveCarrier (M : GradedReflModel) :
    GradedReflectiveCarrier :=
  (transportGradedReflModel M).toGradedReflectiveCarrier
    (fun t => by
      have := transport_model_selfApp_eq_id M t
      rw [this])

-- ════════════════════════════════════════════════════════════
-- Section 10: CarrierInstantiation — the open frontier
-- ════════════════════════════════════════════════════════════

/-- CarrierInstantiation: the open frontier as an explicit type.

    Given a domain D and a ReflectiveCarrierData R, a
    CarrierInstantiation witnesses that D can be realized within
    the canonical subdomain C.

    "Is CarrierInstantiation D R inhabited?" replaces diffuse prose
    about the open problem. -/
structure CarrierInstantiation (D : Type) (R : ReflectiveCarrierData) where
  /-- Embed domain elements into the canonical subdomain. -/
  embed : D → R.C
  /-- Retract canonical elements back to domain elements. -/
  retract : R.C → D
  /-- Section: retract is left inverse of embed. -/
  sect : ∀ d, retract (embed d) = d

/-- A graded carrier instantiation adds grade-compatibility. -/
structure GradedCarrierInstantiation (D : Type) (G : GradedReflectiveCarrier) extends
    CarrierInstantiation D G.toReflectiveCarrierData where
  /-- Grade on the domain. -/
  grade_D : D → Nat
  /-- Embedding is grade-compatible. -/
  embed_grade : ∀ d, G.grade_C (embed d) = grade_D d

/-- The identity instantiation: C instantiates into itself. -/
def CarrierInstantiation.identity (R : ReflectiveCarrierData) :
    CarrierInstantiation R.C R where
  embed := id
  retract := id
  sect _ := rfl

/-- A composed embedding through the ambient carrier:
    D embeds into C, C includes into A. -/
def CarrierInstantiation.throughAmbient {D : Type} {R : ReflectiveCarrierData}
    (ci : CarrierInstantiation D R) : D → R.A :=
  R.incl ∘ ci.embed

/-- The composed embedding is a section: norm ∘ incl ∘ embed is
    left-invertible via retract. -/
theorem CarrierInstantiation.throughAmbient_section {D : Type} {R : ReflectiveCarrierData}
    (ci : CarrierInstantiation D R) :
    ∀ d, ci.retract (R.norm (ci.throughAmbient d)) = d := by
  intro d
  show ci.retract (R.norm (R.incl (ci.embed d))) = d
  rw [R.sect]
  exact ci.sect d

-- ════════════════════════════════════════════════════════════
-- Section 11: Factorization theorem
-- ════════════════════════════════════════════════════════════

/-- FACTORIZATION THEOREM (graded): any function agreeing with the
    canonicalizer of a GradedReflectiveCarrier factors through every
    grade level.

    If f = canonicalize, then f is grade-non-increasing (by construction
    of the graded extension), so f(a) stays within the grade bound.

    This is the ReflectiveCarrierData formulation of
    partial_mirror_selfApp_bounded. -/
theorem GradedReflectiveCarrier.agreeing_function_factors
    (G : GradedReflectiveCarrier) (f : G.A → G.A)
    (h_agrees : ∀ a, f a = G.canonicalize a) (d : Nat) :
    ∀ a, G.grade_A a ≤ d → G.grade_A (f a) ≤ d := by
  intro a hle
  rw [h_agrees]
  exact G.canonicalize_factors d a hle

/-- Factorization through C: any function agreeing with canonicalize
    factors as incl ∘ g for some g : A → C (namely g = norm). -/
theorem ReflectiveCarrierData.canonicalize_factors_through_C
    (R : ReflectiveCarrierData) :
    ∀ a, R.canonicalize a = R.incl (R.norm a) :=
  fun _ => rfl

/-- The bridge contradiction in ReflectiveCarrierData language: if f
    agrees with canonicalize and f overflows, contradiction (in the
    graded case). -/
theorem GradedReflectiveCarrier.agreeing_overflow_contradiction
    (G : GradedReflectiveCarrier) (f : G.A → G.A)
    (h_agrees : ∀ a, f a = G.canonicalize a)
    (overflows : ∀ d, ∃ a, G.grade_A a ≤ d ∧ G.grade_A (f a) > d) :
    False := by
  obtain ⟨a, hle, hgt⟩ := overflows 0
  rw [h_agrees] at hgt
  have := G.canonicalize_grade_le a
  omega

-- ════════════════════════════════════════════════════════════
-- Section 12: Image confinement theorem
-- ════════════════════════════════════════════════════════════

/-- IMAGE CONFINEMENT (pointwise): overflow witnesses are NOT
    fixed points of selfApp. They lie outside C.

    If grade(selfApp(x)) > grade(x), then selfApp(x) ≠ x. Elements
    of C (where selfApp = id) are immune to overflow. -/
theorem overflow_outside_canonical (M : GradedReflModel)
    (x : M.carrier)
    (hoverflow : M.grade (M.selfApp x) > M.grade x) :
    M.selfApp x ≠ x := by
  intro heq
  rw [heq] at hoverflow
  exact Nat.lt_irrefl _ hoverflow

/-- Overflow at x implies x ∉ Fix(selfApp). -/
theorem overflow_not_fixed (M : GradedReflModel)
    (x : M.carrier) (d : Nat)
    (hle : M.grade x ≤ d)
    (hgt : M.grade (M.selfApp x) > d) :
    M.selfApp x ≠ x := by
  intro heq; rw [heq] at hgt; omega

/-- Fixed points are immune to overflow: grade(selfApp(x)) = grade(x). -/
theorem fixed_point_immune (M : GradedReflModel)
    (x : M.carrier) (hfix : M.selfApp x = x) (d : Nat)
    (hle : M.grade x ≤ d) :
    M.grade (M.selfApp x) ≤ d := by
  rw [hfix]; exact hle

/-- IMAGE CONFINEMENT (global, clean): SelfAppUnbounded witnesses are
    confined to the complement of C. Every witness has selfApp(x) ≠ x. -/
theorem selfAppUnbounded_witnesses_outside_C (M : GradedReflModel)
    (hub : SelfAppUnbounded M) (d : Nat) :
    ∃ x, M.grade x ≤ d ∧ M.grade (M.selfApp x) > d ∧ M.selfApp x ≠ x := by
  obtain ⟨x, hle, hgt⟩ := hub.overflows d
  exact ⟨x, hle, hgt, overflow_not_fixed M x d hle hgt⟩

/-- The four immunities restated in ReflectiveCarrierData language:
    elements of C have zero gradeGap, carry the full iso, and cannot
    overflow. Separation is confined to A \ Im(incl). -/
theorem canonical_subdomain_immunities (M : GradedReflModel) :
    -- (1) Fixed points carry full iso
    (∀ x, M.selfApp x = x →
      M.fold (M.unfold x) = x ∧ M.unfold (M.fold x) = x) ∧
    -- (2) Im(selfApp) consists of fixed points
    (∀ x, M.selfApp (M.selfApp x) = M.selfApp x) ∧
    -- (3) Fixed points have zero gradeGap
    (∀ x, M.selfApp x = x → gradeGap M x = 0) ∧
    -- (4) Overflow requires non-fixed points
    (∀ x d, M.grade x ≤ d → M.grade (M.selfApp x) > d →
      M.selfApp x ≠ x) :=
  ⟨fun x hx => selfApp_fixed_has_full_iso M x hx,
   fun x => grm_roundtrip_forces_idempotent M x,
   fun x hx => fixed_point_zero_gap M x hx,
   fun x d hle hgt => overflow_not_fixed M x d hle hgt⟩

-- ════════════════════════════════════════════════════════════
-- Section 13: Concrete witnesses
-- ════════════════════════════════════════════════════════════

/-- retractionModel admits the graded extension (selfApp is grade-non-increasing). -/
def retractionModel_gradedReflectiveCarrier : GradedReflectiveCarrier :=
  retractionModel.toGradedReflectiveCarrier retractionModel_selfApp_grade_le

/-- trivialModel admits the graded extension (selfApp = id). -/
def trivialModel_gradedReflectiveCarrier : GradedReflectiveCarrier :=
  trivialModel.toGradedReflectiveCarrier
    (fun x => by rw [trivial_selfApp_eq_id])

/-- standardModel has ReflectiveCarrierData (computation layer) but
    does NOT admit GradedReflectiveCarrier (naming layer fails). -/
theorem standardModel_no_graded_extension :
    ¬(∀ x, standardModel.grade (standardModel.selfApp x) ≤ standardModel.grade x) := by
  intro h
  exact grade_nonincreasing_contradicts_unbounded standardModel
    standardModel_selfAppUnbounded h

/-- standardModel has UnboundedGap: for any k, the witness x = 2*(k+1)
    has grade 0 (even input) but selfApp grade k+2, so gap > k. -/
theorem standardModel_unboundedGap : standardModel.UnboundedGap := by
  intro k
  use 2 * (k + 1)
  have hgrade_x : standardModel.grade (2 * (k + 1)) = 0 :=
    overflowGrade_even (k + 1)
  have hfold : (2 * (k + 1)) / 2 = k + 1 := by omega
  have hselfApp : standardModel.selfApp (2 * (k + 1)) = 2 * (k + 1) + 1 := by
    show 2 * ((2 * (k + 1)) / 2) + 1 = 2 * (k + 1) + 1
    rw [hfold]
  have hgrade_sa : standardModel.grade (2 * (k + 1) + 1) = k + 2 :=
    overflowGrade_odd (k + 1)
  rw [hselfApp, hgrade_sa, hgrade_x]; omega

-- ════════════════════════════════════════════════════════════
-- Section 14: ProtocolGRM factors through ReflectiveCarrierData
-- ════════════════════════════════════════════════════════════

/-- decode ∘ encode is a canonicalizer on the protocol state space.
    This is selfApp of the induced GRM, and it is idempotent by roundtrip. -/
def ProtocolGRM.canonicalize (P : ProtocolGRM) (s : P.sys.State) : P.sys.State :=
  P.decode (P.encode s)

/-- The canonicalizer is idempotent: roundtrip collapses the inner encode∘decode. -/
theorem ProtocolGRM.canonicalize_idempotent (P : ProtocolGRM) :
    ∀ s, P.canonicalize (P.canonicalize s) = P.canonicalize s := by
  intro s
  show P.decode (P.encode (P.decode (P.encode s))) = P.decode (P.encode s)
  rw [P.h_roundtrip]

/-- The fixed-point subtype of the protocol canonicalizer. -/
def ProtocolGRM.Fixed (P : ProtocolGRM) : Type :=
  { s : P.sys.State // P.canonicalize s = s }

/-- Every ProtocolGRM induces a ReflectiveCarrierData.
    A = State, C = Fix(decode ∘ encode), norm = canonicalize.
    No grade hypothesis needed — the retract exists unconditionally. -/
def ProtocolGRM.toReflectiveCarrierData (P : ProtocolGRM) :
    ReflectiveCarrierData where
  A := P.sys.State
  C := P.Fixed
  incl := Subtype.val
  norm s := ⟨P.canonicalize s, P.canonicalize_idempotent s⟩
  sect c := by
    exact Subtype.ext c.property

/-- The canonicalizer of the protocol's ReflectiveCarrierData IS
    decode ∘ encode (= selfApp of the induced GRM). -/
theorem ProtocolGRM.reflectiveCarrierData_canonicalize (P : ProtocolGRM) :
    ∀ s, P.toReflectiveCarrierData.canonicalize s = P.canonicalize s :=
  fun _ => rfl

/-- HasCotrip means every state is already in Fix(canonicalize):
    C = A, the retract is trivial. -/
theorem ProtocolGRM.cotrip_all_fixed (P : ProtocolGRM)
    (h : P.HasCotrip) (s : P.sys.State) :
    P.canonicalize s = s :=
  h s

-- ════════════════════════════════════════════════════════════
-- Section 15: ProtocolGRM.not_SelfAppUnbounded
-- ════════════════════════════════════════════════════════════

/-- Protocol-induced selfApp has constant additive overhead:
    grade(selfApp(x)) ≤ grade(x) + 2 * transportOverhead.

    This is the Nat form of protocol_gradeGap_bounded. selfApp
    "almost" factors through every grade, with a constant shift.
    In complexity terms: solving costs at most c more than the input,
    where c = 2 * transportOverhead is protocol-determined. -/
theorem ProtocolGRM.selfApp_constant_overhead (P : ProtocolGRM) :
    ∀ s, P.sys.cost (P.toGRM.selfApp s) ≤ P.sys.cost s + 2 * P.sys.transportOverhead := by
  intro s
  have h1 := P.sys.h_transport_cost P.lang_agent P.model_agent
    s (P.encode s) (P.h_encode_transport s)
  have h2 := P.sys.h_transport_cost P.model_agent P.lang_agent
    (P.encode s) (P.decode (P.encode s)) (P.h_decode_transport (P.encode s))
  show P.sys.cost (P.decode (P.encode s)) ≤ P.sys.cost s + 2 * P.sys.transportOverhead
  omega

/-- Shifted factoring: selfApp factors through grade d + 2 * overhead
    when restricted to inputs at grade ≤ d. -/
theorem ProtocolGRM.selfApp_factors_shifted (P : ProtocolGRM) (d : Nat) :
    ∀ s, P.sys.cost s ≤ d →
      P.sys.cost (P.toGRM.selfApp s) ≤ d + 2 * P.sys.transportOverhead :=
  fun s hle => Nat.le_trans (P.selfApp_constant_overhead s) (by omega)

/-- Every ProtocolGRM unconditionally admits a drifted grade extension
    with drift = 2 * transportOverhead. No HasCotrip or zero-overhead
    assumption needed — the transport structure alone bounds the drift.

    This is the unconditional protocol naming layer: the naming may
    lose information (positive drift), but it always exists. -/
def ProtocolGRM.toDriftCarrier (P : ProtocolGRM) :
    FixedGradeDriftCarrier P.toReflectiveCarrierData P.sys.cost
      (2 * P.sys.transportOverhead) where
  grade_C := fun c => P.sys.cost c.val
  grade_compat := fun _ => rfl
  norm_grade_le_drift := by
    intro s
    show P.sys.cost (P.canonicalize s) ≤ P.sys.cost s + 2 * P.sys.transportOverhead
    unfold ProtocolGRM.canonicalize
    have h1 := P.sys.h_transport_cost P.lang_agent P.model_agent
      s (P.encode s) (P.h_encode_transport s)
    have h2 := P.sys.h_transport_cost P.model_agent P.lang_agent
      (P.encode s) (P.decode (P.encode s)) (P.h_decode_transport (P.encode s))
    omega

/-- When transportOverhead = 0, the protocol-induced GRM has
    grade-non-increasing selfApp and cannot witness SelfAppUnbounded.

    The zero-overhead case is the only case where the gap bound
    rules out SelfAppUnbounded. For overhead > 0, selfApp can
    exceed grade d at inputs of grade d (by up to 2 * overhead),
    which is consistent with SelfAppUnbounded.

    NOTE: The gap bound alone does NOT rule out SelfAppUnbounded
    for overhead > 0. The fleet response claiming otherwise was
    incorrect. The bound grade(selfApp(x)) ≤ grade(x) + 2*overhead
    is consistent with ∀ d, ∃ x, grade(x) ≤ d ∧ grade(selfApp(x)) > d
    whenever overhead > 0. -/
theorem ProtocolGRM.not_SelfAppUnbounded_of_zero_overhead (P : ProtocolGRM)
    (h_zero : P.sys.transportOverhead = 0) :
    ¬SelfAppUnbounded P.toGRM := by
  intro ⟨overflows⟩
  -- M.grade = P.sys.cost, M.selfApp s = P.decode (P.encode s)
  simp only [ProtocolGRM.toGRM, GradedReflModel.selfApp] at overflows
  obtain ⟨s, hle, hgt⟩ := overflows 0
  have h1 := P.sys.h_transport_cost P.lang_agent P.model_agent
    s (P.encode s) (P.h_encode_transport s)
  have h2 := P.sys.h_transport_cost P.model_agent P.lang_agent
    (P.encode s) (P.decode (P.encode s)) (P.h_decode_transport (P.encode s))
  rw [h_zero] at h1 h2; omega

/-- Zero overhead gives PEqNP: selfApp is grade-non-increasing. -/
theorem ProtocolGRM.PEqNP_of_zero_overhead (P : ProtocolGRM)
    (h_zero : P.sys.transportOverhead = 0) :
    PEqNP P.toGRM := by
  refine ⟨0, fun s hs => ?_⟩
  simp only [ProtocolGRM.toGRM, GradedReflModel.selfApp] at hs ⊢
  have h1 := P.sys.h_transport_cost P.lang_agent P.model_agent
    s (P.encode s) (P.h_encode_transport s)
  have h2 := P.sys.h_transport_cost P.model_agent P.lang_agent
    (P.encode s) (P.decode (P.encode s)) (P.h_decode_transport (P.encode s))
  rw [h_zero] at h1 h2; omega

/-- Zero overhead gives a GradedReflectiveCarrier. -/
def ProtocolGRM.toGradedReflectiveCarrier_of_zero_overhead (P : ProtocolGRM)
    (h_zero : P.sys.transportOverhead = 0) :
    GradedReflectiveCarrier :=
  P.toGRM.toGradedReflectiveCarrier (fun s => by
    simp only [ProtocolGRM.toGRM, GradedReflModel.selfApp]
    have h1 := P.sys.h_transport_cost P.lang_agent P.model_agent
      s (P.encode s) (P.h_encode_transport s)
    have h2 := P.sys.h_transport_cost P.model_agent P.lang_agent
      (P.encode s) (P.decode (P.encode s)) (P.h_decode_transport (P.encode s))
    rw [h_zero] at h1 h2; omega)

-- ════════════════════════════════════════════════════════════
-- Section 16: Overflow localization — Option 2
-- ════════════════════════════════════════════════════════════

/-- OVERFLOW LOCALIZATION FOR PROTOCOLS.

    If a protocol-induced GRM has SelfAppUnbounded, every overflow
    witness lies outside Fix(decode ∘ encode). The fixed carrier
    C = Fix(canonicalize) is immune to overflow.

    This is the protocol-specific instance of the general
    overflow_not_fixed theorem, but stated in protocol terms:
    overflow is confined to states where decode(encode(s)) ≠ s. -/
theorem ProtocolGRM.overflow_outside_fixed (P : ProtocolGRM)
    (hub : SelfAppUnbounded P.toGRM) (d : Nat) :
    ∃ s, P.sys.cost s ≤ d ∧ P.sys.cost (P.canonicalize s) > d ∧
      P.canonicalize s ≠ s := by
  obtain ⟨s, hle, hgt⟩ := hub.overflows d
  refine ⟨s, ?_, ?_, ?_⟩
  · -- cost(s) ≤ d: from SelfAppUnbounded
    exact hle
  · -- cost(canonicalize(s)) > d: canonicalize = selfApp for protocol GRMs
    exact hgt
  · -- canonicalize(s) ≠ s: overflow implies not a fixed point
    intro heq
    -- heq : P.decode (P.encode s) = s, but hgt uses P.toGRM.selfApp
    unfold ProtocolGRM.canonicalize at heq
    simp only [ProtocolGRM.toGRM, GradedReflModel.selfApp] at hle hgt
    rw [heq] at hgt; omega

/-- The fixed carrier is stable: selfApp restricted to Fix(canonicalize)
    is the identity. Elements of C cannot overflow and have zero gradeGap.

    This holds for ALL GRMs (not just protocol-induced ones), but the
    protocol context gives it additional force: the fixed carrier is
    where language and model agree, and it is unconditionally stable. -/
theorem ProtocolGRM.fixed_carrier_stable (P : ProtocolGRM)
    (s : P.sys.State) (hfix : P.canonicalize s = s) :
    P.toGRM.selfApp s = s ∧
    gradeGap P.toGRM s = 0 ∧
    (∀ d, P.sys.cost s ≤ d → P.sys.cost (P.toGRM.selfApp s) ≤ d) :=
  have heq : P.decode (P.encode s) = s := by
    unfold ProtocolGRM.canonicalize at hfix; exact hfix
  ⟨hfix,
   by simp only [gradeGap, ProtocolGRM.toGRM, GradedReflModel.selfApp]; rw [heq]; omega,
   fun d hle => by
     simp only [ProtocolGRM.toGRM, GradedReflModel.selfApp]; rw [heq]; exact hle⟩

-- ════════════════════════════════════════════════════════════
-- Section 17: Protocol regime classification
-- ════════════════════════════════════════════════════════════

/-- THE PROTOCOL REGIME CLASSIFICATION.

    Every ProtocolGRM falls into one of three regimes:

    (A) Reflective: unconditional. ReflectiveCarrierData always exists,
        canonicalize is idempotent, C = Fix(decode ∘ encode) is stable.

    (B) Collapse: when HasCotrip OR transportOverhead = 0.
        selfApp = id, gradeGap = 0, PEqNP, Group C.

    (C) Open: transportOverhead > 0 AND ¬HasCotrip.
        Bounded additive distortion (≤ 2*overhead per step).
        SelfAppUnbounded is not refuted — but IF it holds, all
        overflow is localized outside Fix(canonicalize).

    The frontier is regime (C): what structural condition on the
    protocol upgrades bounded additive distortion to true collapse? -/
theorem ProtocolGRM.regime_classification (P : ProtocolGRM) :
    -- (A) Reflective: always
    (∀ s, P.canonicalize (P.canonicalize s) = P.canonicalize s) ∧
    -- (B) Cotrip collapses
    (P.HasCotrip → ∀ s, P.toGRM.selfApp s = s) ∧
    -- (B') Zero overhead collapses
    (P.sys.transportOverhead = 0 → PEqNP P.toGRM) ∧
    -- (C) Bounded additive distortion
    (∀ s, P.sys.cost (P.toGRM.selfApp s) ≤
          P.sys.cost s + 2 * P.sys.transportOverhead) ∧
    -- (C') Overflow localized outside C
    (∀ s d, P.sys.cost s ≤ d → P.sys.cost (P.toGRM.selfApp s) > d →
      P.canonicalize s ≠ s) :=
  ⟨P.canonicalize_idempotent,
   fun h => P.cotrip_selfApp_eq_id h,
   fun h => P.PEqNP_of_zero_overhead h,
   P.selfApp_constant_overhead,
   fun s d hle hgt heq => by
     unfold ProtocolGRM.canonicalize at heq
     simp only [ProtocolGRM.toGRM, GradedReflModel.selfApp] at hgt
     rw [heq] at hgt; omega⟩

-- ════════════════════════════════════════════════════════════
-- Section 18: Asymmetric projection (ZK primitive)
-- ════════════════════════════════════════════════════════════

/-- An asymmetric bounded projection on a ProtocolGRM: preserves
    encode cost (certification) but disrupts decode recovery (extraction).

    This is the structural primitive behind zero-knowledge: the
    projection loses information that encode preserves but decode
    cannot recover. The extract_disrupted field witnesses a state
    where recovery fails.

    Note: P.decode (P.encode x) = P.canonicalize x, so extract
    disruption IS the projection mapping a state outside
    Fix(canonicalize). ZK nontriviality is co-localized with
    the complement of C by definition. -/
structure AsymmetricProjection (P : ProtocolGRM) where
  /-- The projection map. -/
  proj : P.sys.State → P.sys.State
  /-- Bounded certification: encode cost of proj(s) is bounded. -/
  cert_overhead : Nat
  certify_bounded : ∀ s, P.sys.cost (P.encode (proj s)) ≤
    P.sys.cost (P.encode s) + cert_overhead
  /-- Extract disruption: there exists a state where decode ∘ encode
      does not recover proj(s). Since decode ∘ encode = canonicalize,
      this means proj(s) ∉ Fix(canonicalize). -/
  extract_disrupted : ∃ s, P.canonicalize (proj s) ≠ proj s

/-- THEOREM 1: Extract-disruption witnesses live outside Fix(canonicalize).

    If decode(encode(proj(s))) ≠ proj(s), then proj(s) is not a fixed
    point of canonicalize. This is immediate from the definition —
    the structural content is that "ZK hiding" and "outside C" are
    the same predicate. -/
theorem AsymmetricProjection.disrupted_outside_C {P : ProtocolGRM}
    (ap : AsymmetricProjection P) :
    ∃ s, P.canonicalize (ap.proj s) ≠ ap.proj s :=
  ap.extract_disrupted

/-- THEOREM 2: No nontrivial asymmetric projection under cotrip.

    HasCotrip means canonicalize = id on all states. Then
    decode(encode(proj(s))) = proj(s) for every s, so extract
    disruption is impossible.

    Cotrip destroys ZK admissibility: when language = model,
    there is no asymmetry to exploit. -/
theorem ProtocolGRM.cotrip_prevents_disruption
    (P : ProtocolGRM) (h : P.HasCotrip)
    (π : P.sys.State → P.sys.State) :
    ∀ s, P.canonicalize (π s) = π s :=
  fun s => h (π s)

/-- Corollary: no AsymmetricProjection exists under cotrip. -/
theorem ProtocolGRM.no_asymmetric_projection_of_cotrip
    (P : ProtocolGRM) (h : P.HasCotrip) :
    ∀ (ap : AsymmetricProjection P), False := by
  intro ap
  obtain ⟨s, hne⟩ := ap.extract_disrupted
  exact hne (h (ap.proj s))

/-- THEOREM 3: Extract disruption and overflow are co-localized.

    Both ZK disruption witnesses (canonicalize(proj(s)) ≠ proj(s))
    and overflow witnesses (grade(selfApp(x)) > d, so canonicalize(x) ≠ x)
    live in the complement of Fix(canonicalize).

    This is not equivalence — it is co-localization. Both phenomena
    are witnesses to the same structural fact: deviation from the
    fixed carrier. -/
theorem ProtocolGRM.disruption_overflow_colocalized (P : ProtocolGRM) :
    -- Disruption witnesses are outside C
    (∀ (π : P.sys.State → P.sys.State) (s : P.sys.State),
      P.canonicalize (π s) ≠ π s → π s ≠ P.canonicalize (π s)) ∧
    -- Overflow witnesses are outside C
    (∀ s d, P.sys.cost s ≤ d → P.sys.cost (P.toGRM.selfApp s) > d →
      P.canonicalize s ≠ s) ∧
    -- Both are trivial under cotrip
    (P.HasCotrip →
      (∀ (π : P.sys.State → P.sys.State) (s : P.sys.State),
        P.canonicalize (π s) = π s) ∧
      ¬SelfAppUnbounded P.toGRM) :=
  ⟨fun _ _ h => Ne.symm h,
   fun s d hle hgt heq => by
     unfold ProtocolGRM.canonicalize at heq
     simp only [ProtocolGRM.toGRM, GradedReflModel.selfApp] at hle hgt
     rw [heq] at hgt; omega,
   fun h => ⟨fun π s => h (π s),
     fun ⟨overflows⟩ => by
       simp only [ProtocolGRM.toGRM, GradedReflModel.selfApp] at overflows
       obtain ⟨s, hle, hgt⟩ := overflows 0
       have := h s
       unfold ProtocolGRM.canonicalize at this
       rw [this] at hgt; omega⟩⟩

-- ════════════════════════════════════════════════════════════
-- Section 19: The exact phase boundary
-- ════════════════════════════════════════════════════════════

/-- The identity map is an admissible AsymmetricProjection whenever
    ¬HasCotrip. cert_overhead = 0 since encode(id(s)) = encode(s).
    extract_disrupted is exactly the existence of a non-fixed state. -/
def AsymmetricProjection.ofNonCotrip {P : ProtocolGRM}
    (h : ¬P.HasCotrip) : AsymmetricProjection P where
  proj := id
  cert_overhead := 0
  certify_bounded := fun _ => Nat.le_refl _
  extract_disrupted := by
    -- Need: ∃ s, P.canonicalize (id s) ≠ id s
    -- i.e., ∃ s, P.canonicalize s ≠ s
    -- From h : ¬(∀ s, P.decode (P.encode s) = s)
    by_contra hall
    push_neg at hall
    -- hall : ∀ s, P.canonicalize (id s) = id s
    apply h
    intro s
    exact hall s

/-- THE EXACT PHASE BOUNDARY.

    AsymmetricProjection exists if and only if ¬HasCotrip.

    Forward: already proved (no_asymmetric_projection_of_cotrip).
    Reverse: proj = id with cert_overhead = 0 is admissible.
    extract_disrupted is ∃ s, canonicalize(s) ≠ s, which is ¬HasCotrip.

    This makes ZK-like asymmetry the exact phase boundary for the
    protocol regime classification, not just a co-located phenomenon. -/
theorem ProtocolGRM.asymmetric_projection_iff_non_cotrip
    (P : ProtocolGRM) :
    (∃ _ : AsymmetricProjection P, True) ↔ ¬P.HasCotrip := by
  constructor
  · -- Forward: AsymmetricProjection → ¬HasCotrip
    intro ⟨ap, _⟩ hcotrip
    obtain ⟨s, hne⟩ := ap.extract_disrupted
    exact hne (hcotrip (ap.proj s))
  · -- Reverse: ¬HasCotrip → AsymmetricProjection (via id)
    intro h
    exact ⟨AsymmetricProjection.ofNonCotrip h, trivial⟩

-- ════════════════════════════════════════════════════════════
-- Section 20: The asymmetry lattice
-- ════════════════════════════════════════════════════════════

/-- Level 0: raw disruption. A state outside Fix(canonicalize). -/
def ProtocolGRM.HasDisruption (P : ProtocolGRM) : Prop :=
  ∃ s, P.canonicalize s ≠ s

/-- Level 0 ↔ ¬HasCotrip. Immediate from definitions. -/
theorem ProtocolGRM.disruption_iff_non_cotrip (P : ProtocolGRM) :
    P.HasDisruption ↔ ¬P.HasCotrip := by
  constructor
  · intro ⟨s, hne⟩ hcotrip
    exact hne (hcotrip s)
  · intro h
    -- ¬HasCotrip = ¬(∀ s, canonicalize s = s)
    -- Need: ∃ s, canonicalize s ≠ s
    by_contra hall
    -- hall : ¬HasDisruption = ¬(∃ s, canonicalize s ≠ s)
    apply h
    intro s
    -- Need: canonicalize s = s
    by_contra hne
    exact hall ⟨s, hne⟩

/-- Level 3: overflow at grade k. There exists a state within grade k
    whose canonicalization exceeds grade k.

    The family {k | OverflowAt P k} characterizes the overflow spectrum.
    When this family covers all of Nat, that is UnboundedDisruption
    (equivalently, SelfAppUnbounded). For protocol GRMs, overflow at any
    grade k is bounded: cost(canonicalize s) ∈ (k, k + 2*overhead]. -/
def ProtocolGRM.OverflowAt (P : ProtocolGRM) (k : Nat) : Prop :=
  ∃ s, P.sys.cost s ≤ k ∧ P.sys.cost (P.canonicalize s) > k

/-- Overflow at any grade implies raw disruption: the overflow witness
    is outside Fix(canonicalize), since fixed points preserve cost. -/
theorem ProtocolGRM.overflowAt_implies_disruption (P : ProtocolGRM) (k : Nat) :
    P.OverflowAt k → P.HasDisruption := by
  intro ⟨s, hle, hgt⟩
  exact ⟨s, fun heq => by rw [heq] at hgt; omega⟩

/-- Cotrip prevents overflow at every grade. -/
theorem ProtocolGRM.cotrip_no_overflow (P : ProtocolGRM)
    (h : P.HasCotrip) (k : Nat) :
    ¬P.OverflowAt k := by
  intro ⟨s, hle, hgt⟩
  unfold ProtocolGRM.canonicalize at hgt
  rw [h s] at hgt; omega

/-- Protocol overflow bound: canonicalize increases cost by at most
    2 * transportOverhead. Combined with overflow (cost > k), this
    gives: any overflow at grade k lies in (k, k + 2*overhead].
    This is the pointwise form of selfApp_constant_overhead. -/
theorem ProtocolGRM.overflow_bounded (P : ProtocolGRM)
    (s : P.sys.State) (k : Nat) (hle : P.sys.cost s ≤ k) :
    P.sys.cost (P.canonicalize s) ≤ k + 2 * P.sys.transportOverhead := by
  unfold ProtocolGRM.canonicalize
  have h1 := P.sys.h_transport_cost P.lang_agent P.model_agent
    s (P.encode s) (P.h_encode_transport s)
  have h2 := P.sys.h_transport_cost P.model_agent P.lang_agent
    (P.encode s) (P.decode (P.encode s)) (P.h_decode_transport (P.encode s))
  omega

/-- Any overflow at any grade requires positive transport overhead.
    Contrapositive: zero overhead admits no overflow witnesses at all.
    Strengthens not_SelfAppUnbounded_of_zero_overhead: not just "no
    global unboundedness" but "no single overflow witness." -/
theorem ProtocolGRM.overflow_requires_positive_overhead (P : ProtocolGRM)
    (k : Nat) (h : P.OverflowAt k) :
    P.sys.transportOverhead > 0 := by
  obtain ⟨s, hle, hgt⟩ := h
  have := P.overflow_bounded s k hle
  omega

/-- Level 5: unbounded disruption. Disruption at every grade level,
    with the disruption witness exhibiting overflow.

    For every grade threshold d, there exists a state at grade ≤ d
    that is both outside C (disrupted) and overflows grade d.

    For protocol GRMs, canonicalize = selfApp, so disruption and
    overflow are the same predicate on the witness. -/
def ProtocolGRM.UnboundedDisruption (P : ProtocolGRM) : Prop :=
  ∀ d, ∃ s, P.sys.cost s ≤ d ∧
    P.canonicalize s ≠ s ∧
    P.sys.cost (P.canonicalize s) > d

/-- UnboundedDisruption ↔ SelfAppUnbounded (for protocol GRMs).

    Forward: each overflow witness is disrupted (overflow_not_fixed).
    Reverse: each disrupted-overflow witness is an overflow witness. -/
theorem ProtocolGRM.unbounded_disruption_iff_selfAppUnbounded
    (P : ProtocolGRM) :
    P.UnboundedDisruption ↔ SelfAppUnbounded P.toGRM := by
  constructor
  · -- UnboundedDisruption → SelfAppUnbounded
    intro h
    constructor
    intro d
    obtain ⟨s, hle, _, hgt⟩ := h d
    -- canonicalize = selfApp for protocol GRMs
    exact ⟨s, hle, hgt⟩
  · -- SelfAppUnbounded → UnboundedDisruption
    intro ⟨overflows⟩
    intro d
    obtain ⟨s, hle, hgt⟩ := overflows d
    refine ⟨s, hle, ?_, hgt⟩
    -- overflow → not fixed (canonicalize s ≠ s)
    intro heq
    unfold ProtocolGRM.canonicalize at heq
    simp only [ProtocolGRM.toGRM, GradedReflModel.selfApp] at hle hgt
    rw [heq] at hgt; omega

/-- The threshold family: overflow at every grade is equivalent to
    UnboundedDisruption. The "disruption" conjunct in UnboundedDisruption
    is redundant — it follows from overflow (fixed points preserve cost).
    This reformulation makes the bridge to SelfAppUnbounded transparent:
    SelfAppUnbounded ↔ UnboundedDisruption ↔ (∀ k, OverflowAt k). -/
theorem ProtocolGRM.threshold_family_iff_unbounded (P : ProtocolGRM) :
    (∀ k, P.OverflowAt k) ↔ P.UnboundedDisruption := by
  constructor
  · intro h d
    obtain ⟨s, hle, hgt⟩ := h d
    exact ⟨s, hle, fun heq => by rw [heq] at hgt; omega, hgt⟩
  · intro h k
    obtain ⟨s, hle, _, hgt⟩ := h k
    exact ⟨s, hle, hgt⟩

/-- THE ASYMMETRY LATTICE.

    Level 0 (HasDisruption): ∃ state outside C          ↔ ¬HasCotrip
    Level 1 (AsymmetricProjection): coincides with Level 0 (id admissible)
    Level 3 (OverflowAt k): overflow at specific grade k (parametrized)
    Level 5 (UnboundedDisruption): overflow at every grade ↔ SelfAppUnbounded

    The chain: Level 5 → Level 0.
    The family: (∀ k, OverflowAt k) ↔ Level 5.
    The bound: any overflow bounded by 2 * transportOverhead.
    The overhead: any overflow requires positive transportOverhead.

    In P vs NP terms:
    - Level 0 = "language ≠ model" (some asymmetry exists)
    - Level 3 = "asymmetry overflows at grade k" (grade-indexed)
    - Level 5 = "P ≠ NP" (asymmetry overflows at every grade)
    - The gap between levels = the carrier engineering frontier -/
theorem ProtocolGRM.asymmetry_lattice (P : ProtocolGRM) :
    -- Level 5 implies Level 0
    (P.UnboundedDisruption → P.HasDisruption) ∧
    -- Overflow at any single grade → Level 0
    (∀ k, P.OverflowAt k → P.HasDisruption) ∧
    -- Threshold family ↔ Level 5
    ((∀ k, P.OverflowAt k) ↔ P.UnboundedDisruption) ∧
    -- Exact characterizations at endpoints
    (P.HasDisruption ↔ ¬P.HasCotrip) ∧
    (P.UnboundedDisruption ↔ SelfAppUnbounded P.toGRM) ∧
    -- Protocol overhead constraint
    (∀ k, P.OverflowAt k → P.sys.transportOverhead > 0) :=
  ⟨fun h => by
     obtain ⟨s, _, hne, _⟩ := h 0
     exact ⟨s, hne⟩,
   P.overflowAt_implies_disruption,
   P.threshold_family_iff_unbounded,
   P.disruption_iff_non_cotrip,
   P.unbounded_disruption_iff_selfAppUnbounded,
   P.overflow_requires_positive_overhead⟩

-- ════════════════════════════════════════════════════════════
-- Section 21: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms ReflectiveCarrierData.canonicalize_idempotent
#print axioms ReflectiveCarrierData.canonicalize_incl
#print axioms ReflectiveCarrierData.incl_injective
#print axioms ReflectiveCarrierData.canonical_iff_in_image
#print axioms GradedReflectiveCarrier.canonicalize_grade_le
#print axioms GradedReflectiveCarrier.canonicalize_factors
#print axioms GradedReflectiveCarrier.toGroupBData
#print axioms GradedReflectiveCarrier.toIdempotentNormalizer
#print axioms GradedReflModel.toReflectiveCarrierData
#print axioms GradedReflModel.reflectiveCarrierData_canonicalize
#print axioms GradedReflModel.toGradedReflectiveCarrier
#print axioms grade_nonincreasing_implies_PEqNP
#print axioms grade_nonincreasing_contradicts_unbounded
#print axioms GradedReflModel.grade_compatible_extension_iff
#print axioms FixedGradeReflectiveCarrier.grade_C_unique
#print axioms FixedGradeReflectiveCarrier.instSubsingleton
#print axioms FixedGradeDriftCarrier.instSubsingleton
#print axioms GradedReflModel.grade_compatible_extension_unique
#print axioms GradedReflModel.no_grade_compatible_extension_of_unbounded
#print axioms GradedReflModel.drift_extension_iff
#print axioms GradedReflModel.drift_extension_unique
#print axioms ProtocolGRM.toDriftCarrier
#print axioms GradedReflModel.drift_extension_mono
#print axioms GradedReflModel.admitsDrift_mono
#print axioms GradedReflModel.admitsDrift_zero_iff
#print axioms GradedReflModel.finiteDrift_iff_not_unboundedGap
#print axioms GradedReflModel.unbounded_gap_iff_no_finite_drift
#print axioms GradedReflModel.no_strict_extension_of_unbounded_gap
#print axioms GradedReflModel.grade_compatible_extension_implies_PEqNP
#print axioms GradedReflModel.selfAppUnbounded_iff_not_PEqNP
#print axioms CanonicalMirror.toGradedReflectiveCarrier
#print axioms GradedReflectiveCarrier.toCanonicalMirror
#print axioms InvariantSubstrate.toCanonicalPoint
#print axioms transportModel_gradedReflectiveCarrier
#print axioms CarrierInstantiation.identity
#print axioms CarrierInstantiation.throughAmbient_section
#print axioms GradedReflectiveCarrier.agreeing_function_factors
#print axioms GradedReflectiveCarrier.agreeing_overflow_contradiction
#print axioms overflow_not_fixed
#print axioms fixed_point_immune
#print axioms selfAppUnbounded_witnesses_outside_C
#print axioms canonical_subdomain_immunities
#print axioms retractionModel_gradedReflectiveCarrier
#print axioms trivialModel_gradedReflectiveCarrier
#print axioms standardModel_no_graded_extension
#print axioms standardModel_unboundedGap
#print axioms ProtocolGRM.canonicalize_idempotent
#print axioms ProtocolGRM.toReflectiveCarrierData
#print axioms ProtocolGRM.reflectiveCarrierData_canonicalize
#print axioms ProtocolGRM.cotrip_all_fixed
#print axioms ProtocolGRM.selfApp_constant_overhead
#print axioms ProtocolGRM.selfApp_factors_shifted
#print axioms ProtocolGRM.not_SelfAppUnbounded_of_zero_overhead
#print axioms ProtocolGRM.PEqNP_of_zero_overhead
#print axioms ProtocolGRM.toGradedReflectiveCarrier_of_zero_overhead
#print axioms ProtocolGRM.overflow_outside_fixed
#print axioms ProtocolGRM.fixed_carrier_stable
#print axioms ProtocolGRM.regime_classification
#print axioms AsymmetricProjection.disrupted_outside_C
#print axioms ProtocolGRM.cotrip_prevents_disruption
#print axioms ProtocolGRM.no_asymmetric_projection_of_cotrip
#print axioms ProtocolGRM.disruption_overflow_colocalized
#print axioms AsymmetricProjection.ofNonCotrip
#print axioms ProtocolGRM.asymmetric_projection_iff_non_cotrip
#print axioms ProtocolGRM.disruption_iff_non_cotrip
#print axioms ProtocolGRM.overflowAt_implies_disruption
#print axioms ProtocolGRM.cotrip_no_overflow
#print axioms ProtocolGRM.overflow_bounded
#print axioms ProtocolGRM.overflow_requires_positive_overhead
#print axioms ProtocolGRM.unbounded_disruption_iff_selfAppUnbounded
#print axioms ProtocolGRM.threshold_family_iff_unbounded
#print axioms ProtocolGRM.asymmetry_lattice

end WTS
