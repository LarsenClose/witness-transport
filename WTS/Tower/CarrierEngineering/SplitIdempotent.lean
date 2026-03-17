/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Tower/CarrierEngineering/SplitIdempotent.lean — ReflectiveCarrierData
as the canonical splitting of an idempotent endomorphism.

Categorical significance: a split idempotent (also called a splitting of
an idempotent, or a retract) is the canonical factorization of an
idempotent e : A → A into a section-retraction pair through the
fixed-point subobject Fix(e). ReflectiveCarrierData IS this splitting,
not a bespoke construction. This file makes that identification explicit.

The equivalence:

  SplitIdempotent ≃ ReflectiveCarrierData

is witnessed by:
  - toSplitIdempotent: R ↦ (A, incl ∘ norm, idempotent)
  - toReflectiveCarrierData: S ↦ (A, Fix(e), Subtype.val, ⟨e·, idem⟩, sect)

The roundtrip theorems show these are inverses up to the canonicalizer/
endomorphism: the essential data (the idempotent action on A) is
preserved exactly.

Graded and drifted variants carry grade structure and grade bounds
through the splitting, connecting to the regime question.

STATUS: 0 sorry.
-/

import WTS.Tower.CarrierEngineering.ReflectiveCarrierData

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: SplitIdempotent — the abstract structure
-- ════════════════════════════════════════════════════════════

/-- A split idempotent: an endomorphism e : A → A satisfying e ∘ e = e
    (pointwise). This is the abstract categorical notion — a morphism
    that factors through its own image. -/
structure SplitIdempotent where
  /-- The ambient type. -/
  A : Type
  /-- The idempotent endomorphism. -/
  e : A → A
  /-- Idempotence: applying e twice is the same as applying it once. -/
  idem : ∀ a, e (e a) = e a

-- ════════════════════════════════════════════════════════════
-- Section 2: ReflectiveCarrierData → SplitIdempotent
-- ════════════════════════════════════════════════════════════

/-- Every ReflectiveCarrierData gives a SplitIdempotent via the
    canonicalizer incl ∘ norm. Idempotence follows from the section
    property: norm(incl(norm(a))) = norm(a), so
    incl(norm(incl(norm(a)))) = incl(norm(a)). -/
def ReflectiveCarrierData.toSplitIdempotent (R : ReflectiveCarrierData) :
    SplitIdempotent where
  A := R.A
  e := R.canonicalize
  idem := R.canonicalize_idempotent

-- ════════════════════════════════════════════════════════════
-- Section 3: SplitIdempotent → ReflectiveCarrierData
-- ════════════════════════════════════════════════════════════

/-- Every SplitIdempotent gives a ReflectiveCarrierData via the
    canonical splitting: C = Fix(e) = { a | e a = a }, incl = val,
    norm a = ⟨e a, idem a⟩, sect from the fixed-point property. -/
def SplitIdempotent.toReflectiveCarrierData (S : SplitIdempotent) :
    ReflectiveCarrierData where
  A := S.A
  C := { a : S.A // S.e a = a }
  incl := Subtype.val
  norm a := ⟨S.e a, S.idem a⟩
  sect c := by
    ext
    show S.e c.val = c.val
    exact c.property

-- ════════════════════════════════════════════════════════════
-- Section 4: Roundtrip theorems
-- ════════════════════════════════════════════════════════════

/-- Roundtrip 1: ReflectiveCarrierData → SplitIdempotent →
    ReflectiveCarrierData preserves the canonicalizer.

    Starting from R, the SplitIdempotent has e = R.canonicalize.
    The reconstructed ReflectiveCarrierData has C = Fix(R.canonicalize),
    and its canonicalize is val ∘ ⟨R.canonicalize ·, ...⟩ = R.canonicalize.
    So the endomorphism on A is preserved exactly. -/
theorem ReflectiveCarrierData.splitIdempotent_roundtrip
    (R : ReflectiveCarrierData) :
    ∀ a, (R.toSplitIdempotent.toReflectiveCarrierData).canonicalize a =
         R.canonicalize a := by
  intro a
  -- LHS: Subtype.val ⟨R.canonicalize a, R.canonicalize_idempotent a⟩
  -- which reduces to R.canonicalize a
  rfl

/-- Roundtrip 2: SplitIdempotent → ReflectiveCarrierData →
    SplitIdempotent preserves the endomorphism.

    Starting from S, the ReflectiveCarrierData has
    canonicalize a = val ⟨S.e a, S.idem a⟩ = S.e a.
    So the reconstructed SplitIdempotent has e = S.e. -/
theorem SplitIdempotent.reflectiveCarrierData_roundtrip
    (S : SplitIdempotent) :
    ∀ a, (S.toReflectiveCarrierData.toSplitIdempotent).e a = S.e a := by
  intro a
  -- LHS: S.toReflectiveCarrierData.canonicalize a
  --     = Subtype.val ⟨S.e a, S.idem a⟩
  --     = S.e a
  rfl

-- ════════════════════════════════════════════════════════════
-- Section 5: GRM connection
-- ════════════════════════════════════════════════════════════

/-- Every GRM's toSplitIdempotent has e = selfApp.

    The chain: GRM → ReflectiveCarrierData (via C = Fix(selfApp),
    norm = selfApp) → SplitIdempotent (via e = canonicalize = selfApp).
    The canonicalize of GRM's ReflectiveCarrierData is definitionally
    selfApp (Subtype.val ∘ ⟨selfApp ·, ...⟩). -/
theorem GradedReflModel.splitIdempotent_is_selfApp (M : GradedReflModel) :
    ∀ x, (M.toReflectiveCarrierData.toSplitIdempotent).e x = M.selfApp x := by
  intro x
  -- e = M.toReflectiveCarrierData.canonicalize
  -- which is Subtype.val ⟨M.selfApp x, ...⟩ = M.selfApp x
  rfl

-- ════════════════════════════════════════════════════════════
-- Section 6: GradedSplitIdempotent
-- ════════════════════════════════════════════════════════════

/-- A graded split idempotent: an idempotent endomorphism with a grade
    function where the idempotent is grade-non-increasing.

    This is the graded version of SplitIdempotent, corresponding to
    GradedReflectiveCarrier (where norm is grade-non-increasing). -/
structure GradedSplitIdempotent extends SplitIdempotent where
  /-- Grade function on A. -/
  grade : A → Nat
  /-- The idempotent is grade-non-increasing. -/
  grade_le : ∀ a, grade (e a) ≤ grade a

/-- Every GradedReflectiveCarrier gives a GradedSplitIdempotent. -/
def GradedReflectiveCarrier.toGradedSplitIdempotent
    (G : GradedReflectiveCarrier) : GradedSplitIdempotent where
  A := G.A
  e := G.canonicalize
  idem := G.toReflectiveCarrierData.canonicalize_idempotent
  grade := G.grade_A
  grade_le := G.canonicalize_grade_le

/-- Every GradedSplitIdempotent gives a GradedReflectiveCarrier
    via the canonical splitting. -/
def GradedSplitIdempotent.toGradedReflectiveCarrier
    (G : GradedSplitIdempotent) : GradedReflectiveCarrier where
  A := G.A
  C := { a : G.A // G.e a = a }
  incl := Subtype.val
  norm a := ⟨G.e a, G.idem a⟩
  sect c := by
    ext
    show G.e c.val = c.val
    exact c.property
  grade_A := G.grade
  grade_C := fun c => G.grade c.val
  grade_compat := fun _ => rfl
  norm_grade_le := G.grade_le

/-- Roundtrip: GradedReflectiveCarrier → GradedSplitIdempotent →
    GradedReflectiveCarrier preserves the canonicalizer. -/
theorem GradedReflectiveCarrier.gradedSplitIdempotent_roundtrip
    (G : GradedReflectiveCarrier) :
    ∀ a, (G.toGradedSplitIdempotent.toGradedReflectiveCarrier).canonicalize a =
         G.canonicalize a := by
  intro a; rfl

/-- Roundtrip: GradedSplitIdempotent → GradedReflectiveCarrier →
    GradedSplitIdempotent preserves the endomorphism. -/
theorem GradedSplitIdempotent.gradedReflectiveCarrier_roundtrip
    (G : GradedSplitIdempotent) :
    ∀ a, (G.toGradedReflectiveCarrier.toGradedSplitIdempotent).e a = G.e a := by
  intro a; rfl

-- ════════════════════════════════════════════════════════════
-- Section 7: DriftedSplitIdempotent
-- ════════════════════════════════════════════════════════════

/-- A drifted split idempotent: an idempotent endomorphism with a grade
    function where the idempotent may increase grade by at most `drift`.

    This is the drifted analogue: grade(e(a)) ≤ grade(a) + drift.
    - drift = 0 recovers GradedSplitIdempotent.
    - drift = 2 * overhead captures protocol GRMs. -/
structure DriftedSplitIdempotent extends SplitIdempotent where
  /-- Grade function on A. -/
  grade : A → Nat
  /-- Drift bound. -/
  drift : Nat
  /-- The idempotent increases grade by at most drift. -/
  grade_le_drift : ∀ a, grade (e a) ≤ grade a + drift

/-- Zero drift recovers a GradedSplitIdempotent. -/
def DriftedSplitIdempotent.toGraded
    (D : DriftedSplitIdempotent) (h : D.drift = 0) :
    GradedSplitIdempotent where
  A := D.A
  e := D.e
  idem := D.idem
  grade := D.grade
  grade_le a := by have := D.grade_le_drift a; omega

/-- A GradedSplitIdempotent is a DriftedSplitIdempotent with drift 0. -/
def GradedSplitIdempotent.toDrifted
    (G : GradedSplitIdempotent) : DriftedSplitIdempotent where
  A := G.A
  e := G.e
  idem := G.idem
  grade := G.grade
  drift := 0
  grade_le_drift a := by have := G.grade_le a; omega

/-- Drift monotonicity: if an idempotent satisfies drift k, it also
    satisfies drift l for any l ≥ k. -/
theorem DriftedSplitIdempotent.drift_mono
    (D : DriftedSplitIdempotent) {l : Nat} (h : D.drift ≤ l) :
    ∀ a, D.grade (D.e a) ≤ D.grade a + l := by
  intro a
  have := D.grade_le_drift a; omega

-- ════════════════════════════════════════════════════════════
-- Section 8: Fixed-point equivalence preservation
-- ════════════════════════════════════════════════════════════

/-- The fixed-point subtype of a SplitIdempotent. -/
def SplitIdempotent.FixedPoints (S : SplitIdempotent) : Type :=
  { a : S.A // S.e a = a }

/-- The canonical subdomain of the induced ReflectiveCarrierData
    IS the fixed-point subtype of the SplitIdempotent (definitionally). -/
theorem SplitIdempotent.fixedPoints_eq_C (S : SplitIdempotent) :
    S.FixedPoints = S.toReflectiveCarrierData.C :=
  rfl

/-- Going through the roundtrip preserves the fixed-point predicate:
    an element is a fixed point of R.canonicalize iff it is a fixed point
    of the reconstructed endomorphism. -/
theorem ReflectiveCarrierData.splitIdempotent_preserves_fixed
    (R : ReflectiveCarrierData) (a : R.A) :
    (R.toSplitIdempotent.toReflectiveCarrierData).canonicalize a = a ↔
    R.canonicalize a = a := by
  -- Both sides are R.canonicalize a = a by roundtrip
  constructor
  · intro h; rwa [R.splitIdempotent_roundtrip] at h
  · intro h; rwa [R.splitIdempotent_roundtrip]

/-- Fixed points of a SplitIdempotent embed into the ambient type via
    inclusion, and every element of A maps to a fixed point via e. -/
theorem SplitIdempotent.fixed_point_section_retraction (S : SplitIdempotent) :
    -- Inclusion followed by e is the identity on fixed points
    (∀ c : S.FixedPoints, S.e c.val = c.val) ∧
    -- e maps every element to a fixed point
    (∀ a, S.e (S.e a) = S.e a) :=
  ⟨fun c => c.property, S.idem⟩

/-- The image of e consists exactly of the fixed points:
    a ∈ Im(e) ↔ e(a) = a.

    Forward: if a = e(b), then e(a) = e(e(b)) = e(b) = a.
    Reverse: if e(a) = a, then a = e(a) ∈ Im(e). -/
theorem SplitIdempotent.image_eq_fixed (S : SplitIdempotent) (a : S.A) :
    (∃ b, S.e b = a) ↔ S.e a = a := by
  constructor
  · intro ⟨b, hb⟩
    rw [← hb, S.idem]
  · intro h
    exact ⟨a, h⟩

-- ════════════════════════════════════════════════════════════
-- Section 9: GRM through SplitIdempotent
-- ════════════════════════════════════════════════════════════

/-- The GRM-to-SplitIdempotent-to-ReflectiveCarrierData roundtrip
    preserves the canonicalizer (which is selfApp). -/
theorem GradedReflModel.splitIdempotent_roundtrip_canonicalize
    (M : GradedReflModel) :
    ∀ x, (M.toReflectiveCarrierData.toSplitIdempotent.toReflectiveCarrierData).canonicalize x =
         M.selfApp x := by
  intro x
  -- By transitivity of the two roundtrip theorems
  rw [M.toReflectiveCarrierData.splitIdempotent_roundtrip,
      M.reflectiveCarrierData_canonicalize]

/-- A GRM with grade-non-increasing selfApp gives a GradedSplitIdempotent. -/
def GradedReflModel.toGradedSplitIdempotent (M : GradedReflModel)
    (h_le : ∀ x, M.grade (M.selfApp x) ≤ M.grade x) :
    GradedSplitIdempotent where
  A := M.carrier
  e := M.selfApp
  idem := grm_roundtrip_forces_idempotent M
  grade := M.grade
  grade_le := h_le

/-- A GRM with bounded selfApp gives a DriftedSplitIdempotent. -/
def GradedReflModel.toDriftedSplitIdempotent (M : GradedReflModel) (k : Nat)
    (h_le : ∀ x, M.grade (M.selfApp x) ≤ M.grade x + k) :
    DriftedSplitIdempotent where
  A := M.carrier
  e := M.selfApp
  idem := grm_roundtrip_forces_idempotent M
  grade := M.grade
  drift := k
  grade_le_drift := h_le

/-- Every ProtocolGRM gives a DriftedSplitIdempotent with
    drift = 2 * transportOverhead. -/
def ProtocolGRM.toDriftedSplitIdempotent (P : ProtocolGRM) :
    DriftedSplitIdempotent where
  A := P.sys.State
  e := P.toGRM.selfApp
  idem := grm_roundtrip_forces_idempotent P.toGRM
  grade := P.sys.cost
  drift := 2 * P.sys.transportOverhead
  grade_le_drift := P.selfApp_constant_overhead

-- ════════════════════════════════════════════════════════════
-- Section 10: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms ReflectiveCarrierData.toSplitIdempotent
#print axioms SplitIdempotent.toReflectiveCarrierData
#print axioms ReflectiveCarrierData.splitIdempotent_roundtrip
#print axioms SplitIdempotent.reflectiveCarrierData_roundtrip
#print axioms GradedReflModel.splitIdempotent_is_selfApp
#print axioms GradedReflectiveCarrier.toGradedSplitIdempotent
#print axioms GradedSplitIdempotent.toGradedReflectiveCarrier
#print axioms GradedReflectiveCarrier.gradedSplitIdempotent_roundtrip
#print axioms GradedSplitIdempotent.gradedReflectiveCarrier_roundtrip
#print axioms DriftedSplitIdempotent.toGraded
#print axioms GradedSplitIdempotent.toDrifted
#print axioms DriftedSplitIdempotent.drift_mono
#print axioms SplitIdempotent.fixedPoints_eq_C
#print axioms ReflectiveCarrierData.splitIdempotent_preserves_fixed
#print axioms SplitIdempotent.fixed_point_section_retraction
#print axioms SplitIdempotent.image_eq_fixed
#print axioms GradedReflModel.splitIdempotent_roundtrip_canonicalize
#print axioms GradedReflModel.toGradedSplitIdempotent
#print axioms GradedReflModel.toDriftedSplitIdempotent
#print axioms ProtocolGRM.toDriftedSplitIdempotent

end WTS
