/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/ReturnPath/PartialReturn.lean — Grade behavior of the return path
on partial Lambek subdomains (Group B chains).

For Group B chains (Chains 5/2/3), the return path goes through
PartialLambekData: the cotrip (selfApp = id) holds on a SUBDOMAIN
but not everywhere. This file characterizes the grade behavior:

- On the subdomain: gradeGap = 0 (selfApp = id there)
- Off the subdomain: gradeGap may be nonzero (the carrier engineering gap)
- If the subdomain is cofinal (RelevantSubdomain), then SelfAppUnbounded
  is contradicted — the partial bridge from OmegaChainCompletion
- The carrier engineering gap = how much of the carrier lies OUTSIDE
  the PartialLambekData domain

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.ReturnPath.Naming.GradeGapMeasure
import WTS.Transport.OmegaChainCompletion
import WTS.Tower.CarrierEngineering

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: On-subdomain gradeGap = 0
-- ════════════════════════════════════════════════════════════

/-- On the partial Lambek domain, gradeGap = 0.

    PartialLambekData.cotrip_on gives selfApp(x) = x for x in the domain.
    Therefore gradeGap(M, x) = grade(selfApp(x)) - grade(x) = 0. -/
theorem partialLambek_zero_gap (M : GradedReflModel)
    (P : PartialLambekData M) (x : M.carrier) (hx : P.domain x) :
    gradeGap M x = 0 := by
  simp only [gradeGap, GradedReflModel.selfApp]
  rw [P.cotrip_on x hx]
  omega

-- ════════════════════════════════════════════════════════════
-- Section 2: Off-subdomain gradeGap may be nonzero
-- ════════════════════════════════════════════════════════════

/-- Elements outside the partial Lambek domain can have nonzero gradeGap.

    This is the carrier engineering gap measured via gradeGap: the domain
    where selfApp = id does not cover the full carrier, and outside it,
    selfApp may shift grade.

    Witnessed by retractionModel with domain = even numbers. On evens,
    selfApp(x) = 2*(x/2) = x, so gradeGap = 0. On odds, selfApp(1) = 0,
    so gradeGap(1) = -1 ≠ 0. -/
theorem off_domain_gap_can_be_nonzero :
    ∃ (M : GradedReflModel) (P : PartialLambekData M),
      ∃ x, ¬P.domain x ∧ gradeGap M x ≠ 0 := by
  refine ⟨retractionModel, {
    domain := fun (x : Nat) => x % 2 = 0
    cotrip_on := fun (x : Nat) (hx : x % 2 = 0) => by
      show retractionModel.unfold (retractionModel.fold x) = x
      simp only [retractionModel]
      omega
  }, (1 : Nat), ?_, ?_⟩
  · show ¬((1 : Nat) % 2 = 0); omega
  · have : gradeGap retractionModel (1 : Nat) < 0 :=
      retractionModel_negative_gap_at_one
    omega

-- ════════════════════════════════════════════════════════════
-- Section 3: RelevantSubdomain + SelfAppUnbounded → False
-- ════════════════════════════════════════════════════════════

/-- The partial bridge in gradeGap terms: if the subdomain where
    gradeGap = 0 is cofinal for separation witnesses, then
    SelfAppUnbounded is contradicted.

    This restates partial_bridge (OmegaChainCompletion.lean) through
    the gradeGap lens. The proof: RelevantSubdomain provides cofinality
    and partial cotrip; cofinality lifts any selfApp overflow to a domain
    element; partial cotrip gives selfApp = id there, so gradeGap = 0,
    contradicting the overflow. -/
theorem partial_bridge_via_gradeGap (M : GradedReflModel)
    (R : RelevantSubdomain M) (hub : SelfAppUnbounded M) : False :=
  partial_bridge M R hub

/-- The gradeGap characterization of the partial bridge:
    if gradeGap = 0 on a cofinal subdomain, SelfAppUnbounded fails.

    Equivalent to partial_bridge but stated in grade gap vocabulary. -/
theorem zero_gap_cofinal_contradicts_unbounded (M : GradedReflModel)
    (R : RelevantSubdomain M)
    (_hzero : ∀ x, R.domain x → gradeGap M x = 0)
    (hub : SelfAppUnbounded M) : False :=
  -- The hzero hypothesis is already implied by R.cotrip_on,
  -- so this reduces to partial_bridge.
  partial_bridge M R hub

-- ════════════════════════════════════════════════════════════
-- Section 4: Carrier engineering gap as subdomain measure
-- ════════════════════════════════════════════════════════════

/-- The carrier engineering gap at a Group B chain is the complement
    of the PartialLambekData domain. This structure captures the
    decomposition: carrier = domain (gradeGap = 0) ∪ complement
    (gradeGap possibly nonzero). -/
structure SubdomainDecomposition (M : GradedReflModel) where
  /-- The partial Lambek data providing the domain. -/
  partialData : PartialLambekData M
  /-- On-domain: gradeGap = 0. -/
  on_domain_zero : ∀ x, partialData.domain x → gradeGap M x = 0
  /-- Off-domain: selfApp may differ from id. -/
  off_domain_ne : ∃ x, ¬partialData.domain x ∧ M.selfApp x ≠ x

/-- A SubdomainDecomposition from any PartialLambekData where selfApp ≠ id
    somewhere outside the domain. -/
def SubdomainDecomposition.mk' (M : GradedReflModel)
    (P : PartialLambekData M)
    (hne : ∃ x, ¬P.domain x ∧ M.selfApp x ≠ x) :
    SubdomainDecomposition M where
  partialData := P
  on_domain_zero := partialLambek_zero_gap M P
  off_domain_ne := hne

/-- If the domain covers the full carrier (every element is in the domain),
    then the model has full Lambek data — selfApp = id everywhere. -/
def full_domain_gives_lambek (M : GradedReflModel)
    (P : PartialLambekData M)
    (hfull : ∀ x, P.domain x) :
    LambekData M where
  cotrip x := P.cotrip_on x (hfull x)

/-- If the domain covers the full carrier, gradeGap = 0 everywhere. -/
theorem full_domain_zero_gap (M : GradedReflModel)
    (P : PartialLambekData M)
    (hfull : ∀ x, P.domain x) :
    ∀ x, gradeGap M x = 0 :=
  fun x => partialLambek_zero_gap M P x (hfull x)

-- ════════════════════════════════════════════════════════════
-- Section 5: Compatible on subdomain
-- ════════════════════════════════════════════════════════════

/-- On the partial Lambek domain, gradeGap ≤ 0 (in fact = 0).
    This connects to compatible_iff_nonpositive_gap: the restriction
    to the domain satisfies the Compatible condition. -/
theorem partialLambek_nonpositive_on_domain (M : GradedReflModel)
    (P : PartialLambekData M) (x : M.carrier) (hx : P.domain x) :
    gradeGap M x ≤ 0 := by
  have := partialLambek_zero_gap M P x hx; omega

/-- On the partial Lambek domain, grade is preserved by selfApp.
    Restates zero gap in Nat terms: grade(selfApp(x)) = grade(x). -/
theorem partialLambek_grade_preserved (M : GradedReflModel)
    (P : PartialLambekData M) (x : M.carrier) (hx : P.domain x) :
    M.grade (M.selfApp x) = M.grade x := by
  have := partialLambek_zero_gap M P x hx
  simp only [gradeGap] at this
  omega

/-- On the partial Lambek domain, selfApp factors through every grade.
    This is the subdomain version of compatible_selfApp_factors. -/
theorem partialLambek_selfApp_factors_on_domain (M : GradedReflModel)
    (P : PartialLambekData M) (x : M.carrier) (hx : P.domain x)
    (d : Nat) (hd : M.grade x ≤ d) :
    M.grade (M.selfApp x) ≤ d := by
  rw [partialLambek_grade_preserved M P x hx]
  exact hd

-- ════════════════════════════════════════════════════════════
-- Section 6: Group B data from partial Lambek with full coverage
-- ════════════════════════════════════════════════════════════

/-- If a PartialLambekData domain covers the full carrier, the model
    yields GroupBData (and in fact GroupC — selfApp = id). -/
def groupBData_from_full_partial (M : GradedReflModel)
    (P : PartialLambekData M)
    (hfull : ∀ x, P.domain x) :
    GroupBData M.carrier where
  retract := M.selfApp
  grade := M.grade
  idempotent := grm_roundtrip_forces_idempotent M
  red_grade_le x := by
    have := partialLambek_grade_preserved M P x (hfull x); omega

/-- Full partial Lambek domain implies Compatible. -/
theorem full_partial_compatible (M : GradedReflModel)
    (P : PartialLambekData M)
    (hfull : ∀ x, P.domain x) :
    M.toGradedRetraction.Compatible := by
  intro x
  simp only [GradedReflModel.toGradedRetraction]
  have := partialLambek_grade_preserved M P x (hfull x); omega

/-- Full partial Lambek domain implies PEqNP. -/
theorem full_partial_PEqNP (M : GradedReflModel)
    (P : PartialLambekData M)
    (hfull : ∀ x, P.domain x) :
    PEqNP M :=
  compatible_retraction_gives_PEqNP M (full_partial_compatible M P hfull)

-- ════════════════════════════════════════════════════════════
-- Section 7: The partial return path summary
-- ════════════════════════════════════════════════════════════

/-- THE PARTIAL RETURN PATH: the complete grade characterization
    for Group B chains.

    Given PartialLambekData (cotrip on a subdomain):
    (1) On-domain: gradeGap = 0, selfApp = id, grade preserved
    (2) The domain satisfies the Compatible condition (restricted)
    (3) If the domain is cofinal (RelevantSubdomain), SelfAppUnbounded
        is contradicted — the partial bridge
    (4) The carrier engineering gap = complement of the domain

    The open question for each Group B chain: is the domain cofinal?
    - Chain 5: is the multilinear Boolean fragment cofinal for degree bounds?
    - Chain 2: is the proof complexity fragment cofinal for refutation bounds?
    - Chain 3: is the syntactic fragment cofinal for formula complexity? -/
theorem partial_return_path (M : GradedReflModel) (P : PartialLambekData M) :
    -- (1) gradeGap = 0 on the domain
    (∀ x, P.domain x → gradeGap M x = 0) ∧
    -- (2) grade preserved on the domain
    (∀ x, P.domain x → M.grade (M.selfApp x) = M.grade x) ∧
    -- (3) selfApp = id on the domain
    (∀ x, P.domain x → M.selfApp x = x) :=
  ⟨partialLambek_zero_gap M P,
   fun x hx => partialLambek_grade_preserved M P x hx,
   P.selfApp_eq_id_on⟩

/-- The cofinal case: if the domain is relevant, the full contradiction. -/
theorem partial_return_path_cofinal (M : GradedReflModel)
    (R : RelevantSubdomain M) (hub : SelfAppUnbounded M) : False :=
  partial_bridge M R hub

-- ════════════════════════════════════════════════════════════
-- Section 8: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms partialLambek_zero_gap
#print axioms off_domain_gap_can_be_nonzero
#print axioms partial_bridge_via_gradeGap
#print axioms zero_gap_cofinal_contradicts_unbounded
#print axioms full_domain_gives_lambek
#print axioms partialLambek_nonpositive_on_domain
#print axioms partialLambek_grade_preserved
#print axioms partialLambek_selfApp_factors_on_domain
#print axioms partial_return_path
#print axioms partial_return_path_cofinal

end WTS
