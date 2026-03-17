/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/ReturnPath/ReturnPathAtPositions.lean — Transport model grade structure
at each concrete starting position.

base_vs_transport_contrast (TransportSelfSimilarity) proves that if M has
unbounded selfApp, T(M) has selfApp = id. But it does not characterize the
GRADE STRUCTURE of T(M)'s carriers at different starting positions.

This file answers: what does the return path look like at each of the three
concrete models (trivialModel, standardModel, retractionModel)?

The universal result: for ANY GradedReflModel M, T(M) has gradeGap = 0
everywhere. The transport level is always at the fixed point regardless of
the base model's grade dynamics.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.ReturnPath.Naming.GradeGapMeasure
import WTS.Transport.TransportSelfSimilarity

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Universal result — T(M) has zero gradeGap for any M
-- ════════════════════════════════════════════════════════════

/-- UNIVERSAL ZERO GAP: for any GradedReflModel M, the transport model
    T(M) has gradeGap = 0 everywhere.

    Proof path: transport_model_selfApp_eq_id gives selfApp = id on T(M),
    then selfApp_eq_id_zero_gap converts that to gradeGap = 0.

    This is the formal content of "the transport level is always at the
    fixed point." The base model M can have any grade dynamics — zero gap,
    nonpositive gap, unbounded positive gap — but T(M) always collapses
    to zero gap. The return path at the meta-level is trivial. -/
theorem transport_model_zero_gap (M : GradedReflModel) :
    ∀ t : (transportGradedReflModel M).carrier,
      gradeGap (transportGradedReflModel M) t = 0 :=
  selfApp_eq_id_zero_gap (transportGradedReflModel M)
    (transport_model_selfApp_eq_id M)

/-- T(M) has nonpositive gap (immediate from zero gap). -/
theorem transport_model_nonpositive_gap (M : GradedReflModel) :
    ∀ t : (transportGradedReflModel M).carrier,
      gradeGap (transportGradedReflModel M) t ≤ 0 := by
  intro t; have := transport_model_zero_gap M t; omega

-- ════════════════════════════════════════════════════════════
-- Section 2: Transport at trivialModel — already at the fixed point
-- ════════════════════════════════════════════════════════════

/-- T(trivialModel) has zero gradeGap everywhere. Both base and meta
    are at the fixed point. This is the "already there" case:
    trivialModel has selfApp = id (zero gap), and T(trivialModel)
    inherits zero gap universally. -/
theorem transport_trivial_zero_gap :
    ∀ t : (transportGradedReflModel trivialModel).carrier,
      gradeGap (transportGradedReflModel trivialModel) t = 0 :=
  transport_model_zero_gap trivialModel

/-- T(trivialModel) has selfApp = id. -/
theorem transport_trivial_selfApp_eq_id :
    ∀ t : (transportGradedReflModel trivialModel).carrier,
      (transportGradedReflModel trivialModel).selfApp t = t :=
  transport_model_selfApp_eq_id trivialModel

/-- At trivialModel: BOTH base and transport have zero gap.
    No contrast — both levels are at the fixed point. -/
theorem trivial_position_both_zero :
    (∀ x, gradeGap trivialModel x = 0) ∧
    (∀ t : (transportGradedReflModel trivialModel).carrier,
      gradeGap (transportGradedReflModel trivialModel) t = 0) :=
  ⟨trivialModel_zero_gap, transport_trivial_zero_gap⟩

-- ════════════════════════════════════════════════════════════
-- Section 3: Transport at standardModel — infinite gap at base,
--            zero gap at meta
-- ════════════════════════════════════════════════════════════

/-- T(standardModel) has zero gradeGap everywhere, despite
    standardModel itself having unbounded positive gradeGap.

    This is the sharpest contrast: the base model has infinite
    grade gap (selfApp overflows every bound), but the transport
    model is at the fixed point (selfApp = id, zero gap). -/
theorem transport_standard_zero_gap :
    ∀ t : (transportGradedReflModel standardModel).carrier,
      gradeGap (transportGradedReflModel standardModel) t = 0 :=
  transport_model_zero_gap standardModel

/-- T(standardModel) has selfApp = id. -/
theorem transport_standard_selfApp_eq_id :
    ∀ t : (transportGradedReflModel standardModel).carrier,
      (transportGradedReflModel standardModel).selfApp t = t :=
  transport_model_selfApp_eq_id standardModel

/-- At standardModel: base has unbounded positive gap, transport has
    zero gap. The maximum contrast in the answer space. -/
theorem standard_position_contrast :
    -- Base: unbounded positive gap
    (∀ d, ∃ x, standardModel.grade x ≤ d ∧
      gradeGap standardModel x > 0) ∧
    -- Transport: zero gap everywhere
    (∀ t : (transportGradedReflModel standardModel).carrier,
      gradeGap (transportGradedReflModel standardModel) t = 0) :=
  ⟨standardModel_unbounded_gap, transport_standard_zero_gap⟩

-- ════════════════════════════════════════════════════════════
-- Section 4: Transport at retractionModel — nonpositive gap at base,
--            zero gap at meta
-- ════════════════════════════════════════════════════════════

/-- T(retractionModel) has zero gradeGap everywhere.
    The base has nonpositive gap (bounded retraction with
    strictly negative points). The contrast is milder than
    standardModel but still present: the base has nonzero
    gap at some points, while the transport has zero gap
    everywhere. -/
theorem transport_retraction_zero_gap :
    ∀ t : (transportGradedReflModel retractionModel).carrier,
      gradeGap (transportGradedReflModel retractionModel) t = 0 :=
  transport_model_zero_gap retractionModel

/-- T(retractionModel) has selfApp = id. -/
theorem transport_retraction_selfApp_eq_id :
    ∀ t : (transportGradedReflModel retractionModel).carrier,
      (transportGradedReflModel retractionModel).selfApp t = t :=
  transport_model_selfApp_eq_id retractionModel

/-- At retractionModel: base has nonpositive gap with strictly negative
    points, transport has zero gap everywhere. -/
theorem retraction_position_contrast :
    -- Base: nonpositive gap with negative points
    (∀ x, gradeGap retractionModel x ≤ 0) ∧
    (∃ x, gradeGap retractionModel x < 0) ∧
    -- Transport: zero gap everywhere
    (∀ t : (transportGradedReflModel retractionModel).carrier,
      gradeGap (transportGradedReflModel retractionModel) t = 0) :=
  ⟨retractionModel_nonpositive_gap,
   ⟨(1 : Nat), retractionModel_negative_gap_at_one⟩,
   transport_retraction_zero_gap⟩

-- ════════════════════════════════════════════════════════════
-- Section 5: The position spectrum — all three in one theorem
-- ════════════════════════════════════════════════════════════

/-- THE RETURN PATH AT ALL THREE POSITIONS.

    For each of the three concrete models (trivialModel, standardModel,
    retractionModel), the transport model T(M) has gradeGap = 0 everywhere.
    The three positions differ only in the base model's gap:

    (1) trivialModel: base gap = 0 (identity), transport gap = 0
        Both levels at the fixed point. No return path needed.

    (2) standardModel: base gap unbounded positive (separation),
        transport gap = 0.
        Maximum contrast: infinite gap at base, zero at meta.

    (3) retractionModel: base gap ≤ 0 with negative points (bounded
        retraction), transport gap = 0.
        Intermediate contrast: bounded nonzero gap at base, zero at meta.

    The universal pattern: regardless of the base model's gap dynamics,
    the transport level always collapses to zero gap. The return path
    at the meta-level is always trivial because the transport construction
    is a fixed point of the meta-rule (selfApp = id). -/
theorem return_path_at_all_positions :
    -- Position 1: trivialModel — both zero
    ((∀ x, gradeGap trivialModel x = 0) ∧
     (∀ t, gradeGap (transportGradedReflModel trivialModel) t = 0)) ∧
    -- Position 2: standardModel — unbounded base, zero transport
    ((∀ d, ∃ x, standardModel.grade x ≤ d ∧ gradeGap standardModel x > 0) ∧
     (∀ t, gradeGap (transportGradedReflModel standardModel) t = 0)) ∧
    -- Position 3: retractionModel — nonpositive base, zero transport
    ((∀ x, gradeGap retractionModel x ≤ 0) ∧
     (∃ x, gradeGap retractionModel x < 0) ∧
     (∀ t, gradeGap (transportGradedReflModel retractionModel) t = 0)) :=
  ⟨trivial_position_both_zero,
   standard_position_contrast,
   retraction_position_contrast⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: Grade preservation at transport level
-- ════════════════════════════════════════════════════════════

/-- selfApp preserves grade exactly in T(M): grade(selfApp(t)) = grade(t).
    This is the grade-level consequence of zero gap. -/
theorem transport_model_preserves_grade (M : GradedReflModel) :
    ∀ t : (transportGradedReflModel M).carrier,
      (transportGradedReflModel M).grade
        ((transportGradedReflModel M).selfApp t) =
      (transportGradedReflModel M).grade t :=
  zero_gap_preserves_grade (transportGradedReflModel M)
    (transport_model_zero_gap M)

-- ════════════════════════════════════════════════════════════
-- Section 7: The universal contrast theorem
-- ════════════════════════════════════════════════════════════

/-- UNIVERSAL CONTRAST: for any M with unbounded selfApp,
    the base has unbounded positive gradeGap while the transport
    has zero gradeGap everywhere.

    This combines base_vs_transport_contrast (regime level) with
    the grade gap characterization (quantitative level). The regime
    result says PEqNP vs not-PEqNP; the gap result says exactly
    how much grade shifting occurs at each level. -/
theorem universal_grade_contrast (M : GradedReflModel)
    (hub : SelfAppUnbounded M) :
    -- Base: unbounded positive gap
    (∀ d, ∃ x, M.grade x ≤ d ∧ gradeGap M x > 0) ∧
    -- Transport: zero gap everywhere
    (∀ t, gradeGap (transportGradedReflModel M) t = 0) :=
  ⟨unbounded_implies_unbounded_gap M hub,
   transport_model_zero_gap M⟩

-- ════════════════════════════════════════════════════════════
-- Section 8: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms transport_model_zero_gap
#print axioms return_path_at_all_positions
#print axioms universal_grade_contrast

end WTS
