/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Transport/ObstructionInvariance.lean — The obstruction is invariant
under structure-preserving maps between graded reflexive models.

STATUS: Framework exploration. These are proved structural results about
the GRM category (PartialLambekData/RelevantSubdomain preserved by
morphisms). They are NOT on the critical path for any paper's claims.
The papers' bridge results rest on the direct bridges (selfApp =
grade-non-increasing red → SelfAppUnbounded → False), not on cross-model
transport. This file documents what the framework CAN express, not what
the papers claim.

The central result: PartialLambekData pushes forward along any
fold/unfold-commuting map (unconditionally), and RelevantSubdomain
pushes forward along surjective strict morphisms. Combined with
partial_bridge, this gives:

  If ANY chain provides a RelevantSubdomain for its model M₁,
  then every model M₂ that M₁ maps onto via a surjective GRMorphism
  ALSO has a RelevantSubdomain, and so SelfAppUnbounded M₂ → False.

The obstruction is not tied to a specific language. It transfers.
The invariance itself is the obstruction: the same structural barrier
appears in every language connected by a grade-preserving,
fold/unfold-commuting map.
-/

import WTS.Transport.OmegaChainCompletion

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: PartialLambekData pushforward (unconditional)
-- ════════════════════════════════════════════════════════════

/-- PartialLambekData pushes forward along any GRRetraction.

    Given a partial Lambek domain in M₁ and a fold/unfold-commuting,
    grade-non-increasing map φ : M₁ → M₂, the image of the domain
    is a partial Lambek domain in M₂.

    The proof uses only fold/unfold commutation (not grade bounds):

      M₂.selfApp(φ(x))
        = M₂.unfold(M₂.fold(φ(x)))
        = M₂.unfold(φ(M₁.fold(x)))       -- map_fold
        = φ(M₁.unfold(M₁.fold(x)))       -- map_unfold
        = φ(x)                            -- cotrip_on x

    No surjectivity, injectivity, or grade condition is needed.
    The cotrip transfers purely from fold/unfold commutation. -/
def PartialLambekData.pushforward {M₁ M₂ : GradedReflModel}
    (P : PartialLambekData M₁) (φ : GRRetraction M₁ M₂) :
    PartialLambekData M₂ where
  domain := fun y => ∃ x, P.domain x ∧ φ.map x = y
  cotrip_on := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hy
    subst hxy
    rw [← φ.map_fold, ← φ.map_unfold]
    congr 1
    exact P.cotrip_on x hx

/-- PartialLambekData also pushes forward along strict GRMorphisms
    (which are a special case of GRRetractions). -/
def PartialLambekData.pushforward_strict {M₁ M₂ : GradedReflModel}
    (P : PartialLambekData M₁) (φ : GRMorphism M₁ M₂) :
    PartialLambekData M₂ :=
  P.pushforward φ.toRetraction

-- ════════════════════════════════════════════════════════════
-- Section 2: RelevantSubdomain pushforward (surjective morphism)
-- ════════════════════════════════════════════════════════════

/-- RelevantSubdomain pushes forward along surjective strict morphisms.

    This is the main invariance theorem. Given:
    - R : RelevantSubdomain M₁ (partial Lambek + cofinality in M₁)
    - φ : GRMorphism M₁ M₂ (fold/unfold-commuting, grade-preserving)
    - surj : φ.map is surjective

    The image of R under φ is a RelevantSubdomain in M₂.

    Cotrip transfers unconditionally (Section 1). Cofinality transfers
    because exact grade preservation lets us:
    1. Pull back overflow witnesses from M₂ to M₁ (surjectivity)
    2. Verify the grade bounds transfer exactly (map_grade)
    3. Apply R.cofinal in M₁ to get a domain witness
    4. Push the witness forward to M₂ (grade + selfApp preserved)

    The surjectivity condition is necessary: without it, M₂ could
    have overflow witnesses with no preimage in M₁, and R.cofinal
    would have nothing to say about them.

    The grade-exactness condition (GRMorphism vs GRRetraction) is
    necessary for pulling back the grade bound: grade(φ(x)) ≤ d
    must imply grade(x) ≤ d, which requires grade(φ(x)) = grade(x).
    A GRRetraction (grade non-increasing) only gives grade(φ(x)) ≤ grade(x),
    so grade(φ(x)) ≤ d does not imply grade(x) ≤ d. -/
def RelevantSubdomain.pushforward {M₁ M₂ : GradedReflModel}
    (R : RelevantSubdomain M₁) (φ : GRMorphism M₁ M₂)
    (surj : Function.Surjective φ.map) :
    RelevantSubdomain M₂ where
  domain := fun y => ∃ x, R.domain x ∧ φ.map x = y
  cotrip_on := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hy
    subst hxy
    rw [← φ.map_fold, ← φ.map_unfold]
    congr 1
    exact R.cotrip_on x hx
  cofinal := by
    intro d ⟨y, hyd, hysa⟩
    -- Pull back: y has a preimage x in M₁
    obtain ⟨x, hxy⟩ := surj y
    subst hxy
    -- Grade bound pulls back exactly (GRMorphism preserves grade)
    have hxd : M₁.grade x ≤ d := by
      have := φ.map_grade x; omega
    -- selfApp overflow pulls back (map_selfApp + exact grade)
    have hxsa : M₁.grade (M₁.selfApp x) > d := by
      have h1 := φ.map_grade (M₁.selfApp x)
      have h2 := φ.map_selfApp x
      rw [h2] at h1
      -- h1 : M₂.grade (M₂.selfApp (φ.map x)) = M₁.grade (M₁.selfApp x)
      omega
    -- Apply R.cofinal in M₁
    obtain ⟨x', hdom, hxd', hxsa'⟩ := R.cofinal d ⟨x, hxd, hxsa⟩
    -- Push the witness forward to M₂
    refine ⟨φ.map x', ⟨x', hdom, rfl⟩, ?_, ?_⟩
    · -- Grade bound: grade(φ(x')) = grade(x') ≤ d
      have := φ.map_grade x'; omega
    · -- selfApp overflow: grade(selfApp(φ(x'))) > d
      have h1 := φ.map_grade (M₁.selfApp x')
      have h2 := φ.map_selfApp x'
      rw [h2] at h1
      -- h1 : M₂.grade (M₂.selfApp (φ.map x')) = M₁.grade (M₁.selfApp x')
      omega

-- ════════════════════════════════════════════════════════════
-- Section 3: The invariance obstruction
-- ════════════════════════════════════════════════════════════

/-- THE OBSTRUCTION IS INVARIANT.

    If M₁ has a RelevantSubdomain and φ : M₁ → M₂ is a surjective
    strict morphism, then M₂ also has a RelevantSubdomain.

    Combined with partial_bridge: if ANY model in the GRM category
    admits a RelevantSubdomain, then every model it maps onto
    surjectively cannot have unbounded selfApp.

    This is the formal content of "the obstruction transfers across
    languages." A single RelevantSubdomain in one chain propagates
    the contradiction to every chain connected by a surjective
    grade-preserving, fold/unfold-commuting map.

    The invariance itself is the obstruction: you cannot escape the
    structural barrier by changing languages, because the barrier
    transfers along any adequate translation. -/
theorem partial_bridge_invariant {M₁ M₂ : GradedReflModel}
    (R : RelevantSubdomain M₁) (φ : GRMorphism M₁ M₂)
    (surj : Function.Surjective φ.map)
    (hub : SelfAppUnbounded M₂) : False :=
  partial_bridge M₂ (R.pushforward φ surj) hub

/-- Corollary: a RelevantSubdomain in M₁ propagates separation
    to any surjective morphism target.

    If M₁ has a RelevantSubdomain (partial Lambek + cofinality),
    then no surjective-morphism target of M₁ can have PEqNP
    with unbounded selfApp. The obstruction is language-independent. -/
theorem obstruction_propagates_separation {M₁ M₂ : GradedReflModel}
    (R : RelevantSubdomain M₁) (φ : GRMorphism M₁ M₂)
    (surj : Function.Surjective φ.map) :
    ¬SelfAppUnbounded M₂ := by
  intro hub
  exact partial_bridge_invariant R φ surj hub

-- ════════════════════════════════════════════════════════════
-- Section 4: PartialLambekData pullback (injective morphism)
-- ════════════════════════════════════════════════════════════

/-- PartialLambekData pulls back along injective GRMorphisms.

    Dual to pushforward: where pushforward takes the IMAGE of the
    domain, pullback takes the PREIMAGE. The cotrip transfers because:

      φ(M₁.selfApp(x)) = M₂.selfApp(φ(x)) = φ(x)

    and injectivity of φ gives M₁.selfApp(x) = x.

    This direction does not need surjectivity or grade conditions
    beyond what GRMorphism already provides. -/
def PartialLambekData.pullback {M₁ M₂ : GradedReflModel}
    (P : PartialLambekData M₂) (φ : GRMorphism M₁ M₂)
    (inj : Function.Injective φ.map) :
    PartialLambekData M₁ where
  domain := fun x => P.domain (φ.map x)
  cotrip_on := by
    intro x hx
    apply inj
    -- Goal: φ.map (M₁.unfold (M₁.fold x)) = φ.map x
    rw [φ.map_unfold, φ.map_fold]
    -- Goal: M₂.unfold (M₂.fold (φ.map x)) = φ.map x
    exact P.cotrip_on (φ.map x) hx

-- ════════════════════════════════════════════════════════════
-- Section 5: Composition and transitivity
-- ════════════════════════════════════════════════════════════

/-- GRMorphism composition: the composite of two strict morphisms
    is a strict morphism. -/
def GRMorphism.comp {M₁ M₂ M₃ : GradedReflModel}
    (ψ : GRMorphism M₂ M₃) (φ : GRMorphism M₁ M₂) :
    GRMorphism M₁ M₃ where
  map := ψ.map ∘ φ.map
  map_fold x := by simp [Function.comp]; rw [φ.map_fold, ψ.map_fold]
  map_unfold x := by simp [Function.comp]; rw [φ.map_unfold, ψ.map_unfold]
  map_grade x := by simp [Function.comp]; rw [ψ.map_grade, φ.map_grade]

/-- Obstruction invariance is transitive: if M₁ →surj M₂ →surj M₃
    are surjective GRMorphisms and M₁ has a RelevantSubdomain,
    then SelfAppUnbounded M₃ → False. -/
theorem partial_bridge_invariant_transitive {M₁ M₂ M₃ : GradedReflModel}
    (R : RelevantSubdomain M₁)
    (φ : GRMorphism M₁ M₂) (ψ : GRMorphism M₂ M₃)
    (surjφ : Function.Surjective φ.map)
    (surjψ : Function.Surjective ψ.map)
    (hub : SelfAppUnbounded M₃) : False := by
  have surj_comp : Function.Surjective (ψ.comp φ).map := by
    intro z
    obtain ⟨y, hy⟩ := surjψ z
    obtain ⟨x, hx⟩ := surjφ y
    exact ⟨x, by show ψ.map (φ.map x) = z; rw [hx, hy]⟩
  exact partial_bridge_invariant R (ψ.comp φ) surj_comp hub

end WTS
