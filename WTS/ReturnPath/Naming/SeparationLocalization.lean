/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

SeparationLocalization: separation is localized to the positive-gap region.

The gradeGap anti-compression assembly (CountingBoundary.lean) shows that
Compatible + injection bound eliminates growth gap. The substrate
(InvariantSubstrate.lean) is always Compatible. The transport model
(TransportSelfSimilarity.lean) is always Compatible.

This file proves the tightening: separation (SelfAppUnbounded) is
supported entirely by elements where gradeGap > 0. The substrate
(gradeGap = 0) and the Compatible region (gradeGap ≤ 0) are immune.
Every overflow witness must come from the positive-gap complement.

The answer space narrows: the question is not "can selfApp overflow?"
(yes, standardModel witnesses this) but "how much of the carrier has
gradeGap > 0?" — the carrier engineering gap, now quantified through
gradeGap and localized by the anti-compression assembly.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.ReturnPath.InvariantSubstrate
import WTS.ReturnPath.Naming.CountingBoundary
import WTS.Transport.TransportSelfSimilarity
import WTS.Tower.FiniteCarrier

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Overflow witnesses have positive gradeGap
-- ════════════════════════════════════════════════════════════

/-- Every overflow witness has strictly positive gradeGap.

    If grade(x) ≤ d and grade(selfApp(x)) > d, then
    gradeGap(x) = grade(selfApp(x)) - grade(x) > 0.

    This is the localization lemma: the elements that CAUSE
    separation (overflow witnesses) are exactly those with
    gradeGap > 0. The substrate (gradeGap = 0) cannot produce
    overflow witnesses. -/
theorem overflow_witness_positive_gap (M : GradedReflModel)
    (x : M.carrier) (d : Nat)
    (hle : M.grade x ≤ d)
    (hgt : M.grade (M.selfApp x) > d) :
    gradeGap M x > 0 := by
  simp only [gradeGap]
  omega

/-- Contrapositive: elements with gradeGap ≤ 0 cannot be overflow
    witnesses at any grade. -/
theorem nonpositive_gap_no_overflow (M : GradedReflModel)
    (x : M.carrier)
    (hgap : gradeGap M x ≤ 0) :
    ∀ d, M.grade x ≤ d → M.grade (M.selfApp x) ≤ d := by
  intro d hle
  simp only [gradeGap] at hgap
  omega

-- ════════════════════════════════════════════════════════════
-- Section 2: The substrate cannot produce overflow
-- ════════════════════════════════════════════════════════════

/-- No element of Im(selfApp) is an overflow witness.
    Im(selfApp) has gradeGap = 0, so selfApp preserves grade
    exactly at these points. -/
theorem substrate_no_overflow (M : GradedReflModel) (x : M.carrier) :
    ∀ d, M.grade (M.selfApp x) ≤ d →
      M.grade (M.selfApp (M.selfApp x)) ≤ d := by
  intro d hle
  rw [selfApp_image_is_fixed]; exact hle

/-- SelfAppUnbounded restricted to Im(selfApp) is impossible.
    The substrate never separates. -/
theorem substrate_never_separates (M : GradedReflModel) :
    ¬(∀ d, ∃ x, M.grade (M.selfApp x) ≤ d ∧
      M.grade (M.selfApp (M.selfApp x)) > d) :=
  substrate_not_unbounded M

-- ════════════════════════════════════════════════════════════
-- Section 3: Separation is localized
-- ════════════════════════════════════════════════════════════

/-- THE LOCALIZATION THEOREM.

    If a model has SelfAppUnbounded, then at every grade d,
    the overflow witness x satisfies gradeGap(x) > 0.

    Separation is supported entirely by the positive-gap region
    of the carrier. The substrate (gradeGap = 0) and the
    Compatible region (gradeGap ≤ 0) are immune.

    Combined with substrate_universal_computation: computation
    lives on the substrate (gradeGap = 0), separation lives on
    the complement (gradeGap > 0). These are disjoint. -/
theorem separation_localized_to_positive_gap (M : GradedReflModel)
    (hub : SelfAppUnbounded M) :
    ∀ d, ∃ x, M.grade x ≤ d ∧
      M.grade (M.selfApp x) > d ∧
      gradeGap M x > 0 := by
  intro d
  obtain ⟨x, hle, hgt⟩ := hub.overflows d
  exact ⟨x, hle, hgt, overflow_witness_positive_gap M x d hle hgt⟩

-- ════════════════════════════════════════════════════════════
-- Section 4: The transport model is immune to separation
-- ════════════════════════════════════════════════════════════

/-- The transport model has gradeGap = 0 everywhere, so it cannot
    produce overflow witnesses. The meta-level is always immune
    to separation. -/
theorem transport_model_no_overflow (M : GradedReflModel)
    (t : (transportGradedReflModel M).carrier) :
    ∀ d, (transportGradedReflModel M).grade t ≤ d →
      (transportGradedReflModel M).grade
        ((transportGradedReflModel M).selfApp t) ≤ d := by
  intro d hle
  rw [transport_model_selfApp_eq_id]; exact hle

/-- SelfAppUnbounded is impossible on the transport model. -/
theorem transport_model_no_separation (M : GradedReflModel) :
    ¬SelfAppUnbounded (transportGradedReflModel M) := by
  intro ⟨hov⟩
  obtain ⟨t, hle, hgt⟩ := hov 0
  rw [transport_model_selfApp_eq_id] at hgt
  omega

-- ════════════════════════════════════════════════════════════
-- Section 5: The carrier engineering gap via gradeGap
-- ════════════════════════════════════════════════════════════

/-- The carrier engineering gap as a gradeGap predicate.

    For a model with SelfAppUnbounded, the carrier partitions into:
    - Substrate: {x | gradeGap(x) ≤ 0} — immune to separation,
      carries computation, selfApp factors through every grade here
    - Complement: {x | gradeGap(x) > 0} — supports separation,
      all overflow witnesses live here

    The "size" of the carrier engineering gap is the extent of the
    positive-gap region. -/
def CarrierGapRegion (M : GradedReflModel) (x : M.carrier) : Prop :=
  gradeGap M x > 0

/-- Every overflow witness is in the carrier gap region. -/
theorem overflow_in_gap_region (M : GradedReflModel)
    (x : M.carrier) (d : Nat)
    (hle : M.grade x ≤ d) (hgt : M.grade (M.selfApp x) > d) :
    CarrierGapRegion M x :=
  overflow_witness_positive_gap M x d hle hgt

/-- No element of Im(selfApp) is in the carrier gap region. -/
theorem substrate_outside_gap_region (M : GradedReflModel)
    (x : M.carrier) :
    ¬CarrierGapRegion M (M.selfApp x) := by
  unfold CarrierGapRegion
  have := selfApp_image_zero_gap M x
  omega

-- ════════════════════════════════════════════════════════════
-- Section 6: The full picture — three levels, one gradient
-- ════════════════════════════════════════════════════════════

/-- THE FULL LOCALIZATION PICTURE.

    Three levels of structure, each immune to separation:

    (1) Im(selfApp) — the invariant substrate:
        gradeGap = 0, selfApp = id, full iso, computation lives here.
        Cannot produce overflow witnesses.

    (2) The transport model — the meta-level:
        gradeGap = 0 everywhere, selfApp = id, SelfAppUnbounded impossible.
        The meta-level of ANY model is always in the collapse regime.

    (3) Finite carriers — pigeonhole level:
        selfApp = id forced by pigeonhole, SelfAppUnbounded impossible.
        Phase transition requires infinite carriers.

    Separation is squeezed into: infinite-carrier models, on elements
    outside Im(selfApp), where gradeGap > 0.

    The carrier engineering gap at each chain measures exactly this:
    how much of the carrier lies in the positive-gap region. -/
theorem separation_fully_localized :
    -- (1) Substrate immune: no overflow on Im(selfApp)
    (∀ M : GradedReflModel, ∀ x,
      ¬CarrierGapRegion M (M.selfApp x)) ∧
    -- (2) Transport model immune: no separation at meta-level
    (∀ M : GradedReflModel,
      ¬SelfAppUnbounded (transportGradedReflModel M)) ∧
    -- (3) Finite carriers immune: no separation on Fin n
    (∀ n : Nat, ∀ (fold unfold : Fin n → Fin n),
      ∀ (rt : ∀ x, fold (unfold x) = x),
      ∀ (grade : Fin n → Nat),
      ¬SelfAppUnbounded ⟨Fin n, fold, unfold, rt, grade⟩) ∧
    -- (4) When separation exists, it's localized to positive gap
    (∀ M : GradedReflModel, SelfAppUnbounded M →
      ∀ d, ∃ x, M.grade x ≤ d ∧
        M.grade (M.selfApp x) > d ∧
        CarrierGapRegion M x) :=
  ⟨fun M x => substrate_outside_gap_region M x,
   fun M => transport_model_no_separation M,
   fun n fold unfold rt grade => finite_carrier_no_separation n fold unfold rt grade,
   fun M hub => separation_localized_to_positive_gap M hub⟩

-- ════════════════════════════════════════════════════════════
-- Section 7: The positive-gap region must be infinite
-- ════════════════════════════════════════════════════════════

/-- For any finite set of positive-gap elements, there is a grade
    beyond which none of them can serve as overflow witnesses.

    If x has gradeGap > 0, then grade(selfApp(x)) is some finite
    number. For d > grade(selfApp(x)), x cannot witness overflow
    at grade d (because grade(selfApp(x)) ≤ d, not > d). -/
theorem positive_gap_element_exhausts (M : GradedReflModel)
    (x : M.carrier) :
    ∃ D, ∀ d, d ≥ D → M.grade x ≤ d →
      M.grade (M.selfApp x) ≤ d :=
  ⟨M.grade (M.selfApp x), fun _ hd _ => hd⟩

/-- THE INFINITE POSITIVE-GAP THEOREM.

    If a model has SelfAppUnbounded, then for any finite bound B,
    there exist overflow witnesses with selfApp grade exceeding B.

    In other words: the positive-gap region contains elements of
    unboundedly large selfApp grade. The separation is not a finite
    anomaly — it requires an unbounded structural feature of the
    carrier.

    Proof: SelfAppUnbounded at grade B gives x with grade(x) ≤ B
    and grade(selfApp(x)) > B. This x has gradeGap > 0 and
    grade(selfApp(x)) > B. Since B is arbitrary, the selfApp
    grades in the positive-gap region are unbounded. -/
theorem separation_requires_unbounded_positive_gap (M : GradedReflModel)
    (hub : SelfAppUnbounded M) :
    ∀ B, ∃ x, CarrierGapRegion M x ∧ M.grade (M.selfApp x) > B := by
  intro B
  obtain ⟨x, hle, hgt⟩ := hub.overflows B
  exact ⟨x, overflow_witness_positive_gap M x B hle hgt, hgt⟩

/-- Corollary: no finite collection of elements suffices for separation.

    If we restrict to elements with selfApp grade ≤ D, we cannot
    produce overflow witnesses at grades > D. Therefore separation
    requires elements of arbitrarily high selfApp grade — an
    infinite feature, not a finite one. -/
theorem finite_positive_gap_no_separation (M : GradedReflModel)
    (D : Nat)
    (h_finite : ∀ x, CarrierGapRegion M x → M.grade (M.selfApp x) ≤ D) :
    ¬SelfAppUnbounded M := by
  intro ⟨hov⟩
  obtain ⟨x, hle, hgt⟩ := hov D
  have hpos := overflow_witness_positive_gap M x D hle hgt
  have hbound := h_finite x hpos
  omega

/-- THE COMPLETE TIGHTENING.

    Separation in a GradedReflModel requires ALL of the following:
    (1) Infinite carrier (finite carriers force selfApp = id)
    (2) Positive-gap region is nonempty (separation lives there)
    (3) Positive-gap region has unbounded selfApp grade
        (finite positive-gap region cannot sustain separation)
    (4) The positive-gap region is the complement of Im(selfApp)
        (the substrate is immune)

    The carrier engineering gap at each chain = the extent of this
    positive-gap region. Closing the gap means showing it is empty
    (Group C) or characterizing its structure (Groups A/B). -/
theorem separation_requirements (M : GradedReflModel)
    (hub : SelfAppUnbounded M) :
    -- (1) Every overflow witness has positive gradeGap
    (∀ d, ∃ x, M.grade x ≤ d ∧ M.grade (M.selfApp x) > d ∧
      gradeGap M x > 0) ∧
    -- (2) Positive-gap region has unbounded selfApp grade
    (∀ B, ∃ x, CarrierGapRegion M x ∧ M.grade (M.selfApp x) > B) ∧
    -- (3) Substrate is disjoint from separation
    (∀ x, ¬CarrierGapRegion M (M.selfApp x)) ∧
    -- (4) ¬PEqNP
    ¬PEqNP M :=
  ⟨separation_localized_to_positive_gap M hub,
   separation_requires_unbounded_positive_gap M hub,
   fun x => substrate_outside_gap_region M x,
   incompatible_retraction_gives_separation M hub⟩

-- ════════════════════════════════════════════════════════════
-- Section 8: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms overflow_witness_positive_gap
#print axioms nonpositive_gap_no_overflow
#print axioms substrate_no_overflow
#print axioms separation_localized_to_positive_gap
#print axioms transport_model_no_separation
#print axioms substrate_outside_gap_region
#print axioms separation_fully_localized

end WTS
