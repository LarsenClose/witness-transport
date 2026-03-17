/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Transport/OmegaChainCompletion.lean — The D∞ construction as a
formal bridge factory.

The transport self-similarity theorem (TransportSelfSimilarity.lean)
proves that T(M) is a fixed point of the transport construction: it
has selfApp = id, PEqNP, universal consequence closure, and is a
grade-preserving retract of T(T(M)). This file abstracts that pattern
into a general construction: any endofunctor on GradedReflModels that
produces a section-retraction pair with meta-collapse yields the same
fixed-point properties.

## Connection to domain theory

This is the D∞ construction (Scott 1972) realized for graded reflexive
models. The classical D∞ builds a sequence D₀, D₁ = F(D₀), D₂ = F(D₁), ...
with embeddings eₙ : Dₙ → Dₙ₊₁ and projections pₙ : Dₙ₊₁ → Dₙ
satisfying pₙ ∘ eₙ = id, and takes the limit. The limit carries a
Lambek isomorphism D∞ ≅ F(D∞).

In our setting:
- F = transportGradedReflModel (the canonical instance)
- The embeddings are GRM morphisms (transport_lift_morphism)
- The projections are GR retractions (transport_eval_retraction)
- The fixed point has selfApp = id (the meta-level is trivial)
- The Lambek isomorphism is degenerate: fold = unfold = id

## Connection to ConstructiveOmega.lean (in pnp-integrated)

PNP/Foundations/ConstructiveOmega.lean proves the Y combinator at axiom profile ∅ via
ReflData (the categorical Lambek iso [A,L] ≅ L). The connection:
- ReflData.fwd / ReflData.bwd = fold / unfold
- selfApp in ReflCat = unfold ∘ fold = GradedReflModel.selfApp
- omega_fixed_point = the Y combinator equation

The D∞ fixed point has selfApp = id, which means the omega/Y combinator
at the fixed point acts as the identity — every endomorphism on the
fixed point has itself as a fixed point of self-application. This is
the formal content of "the meta-rule has nothing to do."

## The bridge factory

The leverage: instead of each chain independently proving its bridge
to GRM morphism status, a chain proves "my source algebra admits a
GRM endofunctor" and the omega-chain completion produces the full
morphism tower (structural retraction + PolyGRRetraction + regime
functoriality) for free. This is a formal bridge factory.

Chain 4 (CSP): the arity-indexed clone algebra PolClone would need a
reflexive-object completion (inverse limit over arities) to instantiate
as a GRM endofunctor. The D∞ construction IS that completion.

Chain 5 (algebraic proofs): the partial Lambek on Boolean domain would
need extension to a full Lambek to instantiate. The D∞ construction
provides the template for such extension.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Core
import WTS.Transport.WitnessTransportCore
import WTS.Transport.TransportSelfSimilarity

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: GRM Endofunctor
-- ════════════════════════════════════════════════════════════

/-- A GRM endofunctor: an operation on GradedReflModels that produces
    a section-retraction pair with meta-collapse.

    The defining properties:
    - F maps GradedReflModels to GradedReflModels
    - F(M) embeds into F(F(M)) as a strict GRM morphism (section)
    - F(F(M)) retracts onto F(M) as a GR retraction (projection)
    - The retraction-section pair satisfies eval ∘ lift = id
    - F(M) always has selfApp = id (meta-collapse / fixed-point property)

    The meta-collapse is the key axiom: it says F is a "completion"
    functor that always reaches the fixed point in one step. The
    transport construction satisfies this because fold and unfold at
    the transport level are both extensionally the identity (by the
    base model's roundtrip axiom). -/
structure GRMEndofunctor where
  /-- The endofunctor on objects. -/
  F : GradedReflModel → GradedReflModel
  /-- Section: F(M) ↪ F(F(M)) as a strict GRM morphism. -/
  lift : ∀ M, GRMorphism (F M) (F (F M))
  /-- Retraction: F(F(M)) ↞ F(M) as a GR retraction. -/
  eval : ∀ M, GRRetraction (F (F M)) (F M)
  /-- Coherence: eval ∘ lift = id. -/
  roundtrip : ∀ M t, (eval M).map ((lift M).map t) = t
  /-- Meta-collapse: F(M) always has selfApp = id.
      This is the D∞ fixed-point property: applying the operation
      never creates new obstructions at the meta-level. -/
  collapse : ∀ M (t : (F M).carrier), (F M).selfApp t = t

-- ════════════════════════════════════════════════════════════
-- Section 2: Fixed-point properties derived from meta-collapse
-- ════════════════════════════════════════════════════════════

/-- F(M) is in the P=NP regime (immediate from meta-collapse). -/
theorem GRMEndofunctor.F_PEqNP (E : GRMEndofunctor) (M : GradedReflModel) :
    PEqNP (E.F M) := by
  refine ⟨0, fun t ht => ?_⟩
  rw [E.collapse M t]
  exact ht

/-- F(F(M)) also has selfApp = id (meta-collapse applied to F(M)). -/
theorem GRMEndofunctor.FF_collapse (E : GRMEndofunctor) (M : GradedReflModel) :
    ∀ t : (E.F (E.F M)).carrier, (E.F (E.F M)).selfApp t = t :=
  E.collapse (E.F M)

/-- F(F(M)) is in the P=NP regime. -/
theorem GRMEndofunctor.FF_PEqNP (E : GRMEndofunctor) (M : GradedReflModel) :
    PEqNP (E.F (E.F M)) :=
  E.F_PEqNP (E.F M)

/-- The regime match between F(M) and F(F(M)) is forced by the
    morphism structure: the lift is a strict GRM morphism, and
    reflects_PEqNP pulls the regime from F(F(M)) back to F(M). -/
theorem GRMEndofunctor.regime_forced (E : GRMEndofunctor) (M : GradedReflModel) :
    PEqNP (E.F M) :=
  (E.lift M).reflects_PEqNP (E.FF_PEqNP M)

/-- The section-retraction pair is a structural retraction in the
    GRM morphism category: F(M) is a grade-preserving retract of F(F(M)).

    This generalizes structural_retraction from TransportSelfSimilarity. -/
theorem GRMEndofunctor.structural_retraction (E : GRMEndofunctor) (M : GradedReflModel) :
    (∃ φ : GRMorphism (E.F M) (E.F (E.F M)),
      ∃ ψ : GRRetraction (E.F (E.F M)) (E.F M),
        ∀ t, ψ.map (φ.map t) = t) :=
  ⟨E.lift M, E.eval M, E.roundtrip M⟩

/-- The lift (section) is also a PolyGRRetraction (through the hierarchy). -/
def GRMEndofunctor.lift_polyRetraction (E : GRMEndofunctor) (M : GradedReflModel) :
    PolyGRRetraction (E.F M) (E.F (E.F M)) :=
  (E.lift M).toPolyGRRetraction

/-- The eval (retraction) is also a PolyGRRetraction. -/
def GRMEndofunctor.eval_polyRetraction (E : GRMEndofunctor) (M : GradedReflModel) :
    PolyGRRetraction (E.F (E.F M)) (E.F M) :=
  (E.eval M).toPolyGRRetraction

/-- The lift and eval both preserve selfApp (regime functoriality).
    Since selfApp = id at both levels, this is trivially true but
    the proof goes through the general morphism theorem. -/
theorem GRMEndofunctor.lift_preserves_selfApp (E : GRMEndofunctor) (M : GradedReflModel)
    (t : (E.F M).carrier) :
    (E.lift M).map ((E.F M).selfApp t) = (E.F (E.F M)).selfApp ((E.lift M).map t) :=
  (E.lift M).map_selfApp t

theorem GRMEndofunctor.eval_preserves_selfApp (E : GRMEndofunctor) (M : GradedReflModel)
    (tt : (E.F (E.F M)).carrier) :
    (E.eval M).map ((E.F (E.F M)).selfApp tt) = (E.F M).selfApp ((E.eval M).map tt) :=
  (E.eval M).map_selfApp tt

-- ════════════════════════════════════════════════════════════
-- Section 3: The transport construction as canonical instance
-- ════════════════════════════════════════════════════════════

/-- The transport construction is a GRM endofunctor.

    This is the canonical instance: transportGradedReflModel satisfies
    all five axioms of GRMEndofunctor. The proofs are exactly the
    theorems from Sections 15-16 of TransportSelfSimilarity.lean:
    - lift = transport_lift_morphism (Section 15)
    - eval = transport_eval_retraction (Section 15)
    - roundtrip = transport_section_retraction (Section 13)
    - collapse = transport_model_selfApp_eq_id (Section 7) -/
def transportEndofunctor : GRMEndofunctor where
  F := transportGradedReflModel
  lift := transport_lift_morphism
  eval := transport_eval_retraction
  roundtrip := transport_section_retraction
  collapse := transport_model_selfApp_eq_id

/-- The transport endofunctor's fixed-point properties recover the
    transport fixed-point theorem (Section 14). -/
theorem transportEndofunctor_recovers_fixed_point (M : GradedReflModel) :
    (∀ t, (transportGradedReflModel M).selfApp t = t) ∧
    PEqNP (transportGradedReflModel M) :=
  ⟨transportEndofunctor.collapse M, transportEndofunctor.F_PEqNP M⟩

-- ════════════════════════════════════════════════════════════
-- Section 4: The bridge factory
-- ════════════════════════════════════════════════════════════

/-- BRIDGE FACTORY THEOREM.

    Any GRM endofunctor produces the full bridge infrastructure:
    (1) F(M) is in the collapse regime (selfApp = id, PEqNP)
    (2) F(M) ↪ F(F(M)) via a strict GRM morphism (section)
    (3) F(F(M)) ↠ F(M) via a GR retraction (projection)
    (4) The section and retraction compose to the identity
    (5) Both section and retraction are PolyGRRetractions
    (6) Separation in M does NOT propagate to F(M) — the meta-level
        is always in collapse regime

    The leverage: a chain proves "my source algebra admits a
    GRM endofunctor" and gets (1)-(6) for free. No per-chain proof
    of self-similarity, consequence closure, or morphism properties
    is needed — the endofunctor axioms are sufficient.

    What each chain must provide:
    - An endofunctor F on GradedReflModels
    - Lift and eval maps with grade bounds
    - Fold/unfold commutation for both maps
    - The roundtrip identity (eval ∘ lift = id)
    - The meta-collapse property (selfApp = id at F(M))

    The meta-collapse is the hard part — it requires showing that
    F's fold and unfold are extensionally the identity at the meta-level.
    For the transport construction, this follows from M.roundtrip.
    For other chains, this is precisely the Lambek condition:
    fold ∘ unfold = id AND unfold ∘ fold = id at the meta-level. -/
theorem bridge_factory (E : GRMEndofunctor) (M : GradedReflModel) :
    -- (1) Meta-collapse: selfApp = id
    (∀ t, (E.F M).selfApp t = t) ∧
    -- (2) P=NP at the meta-level
    PEqNP (E.F M) ∧
    -- (3) Structural retraction: F(M) ↪ F(F(M)) ↞ F(M)
    (∃ φ : GRMorphism (E.F M) (E.F (E.F M)),
      ∃ ψ : GRRetraction (E.F (E.F M)) (E.F M),
        ∀ t, ψ.map (φ.map t) = t) ∧
    -- (4) Idempotence: F(F(M)) also has selfApp = id
    (∀ t, (E.F (E.F M)).selfApp t = t) :=
  ⟨E.collapse M,
   E.F_PEqNP M,
   E.structural_retraction M,
   E.FF_collapse M⟩

-- ════════════════════════════════════════════════════════════
-- Section 5: Endofunctor from Lambek data
-- ════════════════════════════════════════════════════════════

/-- Lambek data for a GradedReflModel: the fold/unfold pair forms a
    FULL isomorphism (both roundtrip AND cotrip hold).

    When a GradedReflModel has Lambek data, its selfApp = id because:
    selfApp = unfold ∘ fold, and cotrip says unfold(fold(x)) = x.

    Connection to ConstructiveOmega.lean: ReflData A L provides
    fwd : [A,L] → L and bwd : L → [A,L] with fwd_bwd and bwd_fwd.
    At the endomorphism level (A = L), fwd = fold, bwd = unfold,
    bwd_fwd = roundtrip, fwd_bwd = cotrip. -/
structure LambekData (M : GradedReflModel) where
  /-- The reverse roundtrip: unfold(fold(x)) = x (selfApp = id). -/
  cotrip : ∀ x, M.unfold (M.fold x) = x

/-- A model with Lambek data has selfApp = id. -/
theorem LambekData.selfApp_eq_id {M : GradedReflModel} (L : LambekData M) :
    ∀ x, M.selfApp x = x :=
  L.cotrip

/-- A model with Lambek data is in the P=NP regime. -/
theorem LambekData.PEqNP {M : GradedReflModel} (L : LambekData M) :
    PEqNP M := by
  refine ⟨0, fun x hx => ?_⟩
  rw [L.selfApp_eq_id x]; exact hx

/-- The key observation: a GRM endofunctor always produces models with
    Lambek data. The meta-collapse axiom IS the cotrip condition. -/
def GRMEndofunctor.lambekData (E : GRMEndofunctor) (M : GradedReflModel) :
    LambekData (E.F M) where
  cotrip := E.collapse M

/-- LAMBEK FACTORY: given any endofunctor that produces fold/unfold pairs
    where the cotrip holds, the resulting models automatically have
    Lambek data, selfApp = id, PEqNP, and the full bridge infrastructure.

    This connects the D∞ construction to the Lambek isomorphism:
    - ConstructiveOmega.lean: ReflData (Lambek iso) → Y combinator (axiom ∅)
    - OmegaChainCompletion: GRMEndofunctor (D∞ pattern) → bridge factory
    - The bridge: meta-collapse = cotrip = Lambek data

    The Y combinator and the D∞ fixed point are two views of the same
    mathematical structure: a reflexive object where self-application
    is the identity. The Y combinator gives you the fixed-point operator
    (categorical level, axiom ∅). The D∞ construction gives you the
    bridge infrastructure (GRM morphisms, PolyGRRetractions, regime
    functoriality). -/
theorem lambek_factory (E : GRMEndofunctor) (M : GradedReflModel) :
    -- Lambek data exists
    (∃ _ : LambekData (E.F M), True) ∧
    -- selfApp = id (from Lambek)
    (∀ t, (E.F M).selfApp t = t) ∧
    -- PEqNP (from Lambek)
    PEqNP (E.F M) ∧
    -- Full bridge infrastructure
    (∃ φ : GRMorphism (E.F M) (E.F (E.F M)),
      ∃ ψ : GRRetraction (E.F (E.F M)) (E.F M),
        ∀ t, ψ.map (φ.map t) = t) :=
  ⟨⟨E.lambekData M, trivial⟩,
   E.collapse M,
   E.F_PEqNP M,
   E.structural_retraction M⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: Partial Lambek and relevant subdomains
-- ════════════════════════════════════════════════════════════

/-- Partial Lambek data: the cotrip condition holds on a subdomain.

    Full Lambek (LambekData) requires unfold(fold(x)) = x for ALL x.
    Partial Lambek requires it only on a subdomain. The subdomain
    represents the "well-behaved" fragment where the reflexive structure
    is complete — e.g., multilinear polynomials over GF(2) in Chain 5,
    where eval ∘ multilinear_extend = id.

    Elements outside the domain are algebraically present but carry
    no complexity-theoretic content. The separation (if it exists)
    must be witnessed entirely within the domain. -/
structure PartialLambekData (M : GradedReflModel) where
  /-- The subdomain where the Lambek cotrip holds. -/
  domain : M.carrier → Prop
  /-- Cotrip restricted to the subdomain: selfApp = id on domain elements. -/
  cotrip_on : ∀ x, domain x → M.unfold (M.fold x) = x

/-- On the partial Lambek domain, selfApp is the identity. -/
theorem PartialLambekData.selfApp_eq_id_on {M : GradedReflModel}
    (P : PartialLambekData M) (x : M.carrier) (hx : P.domain x) :
    M.selfApp x = x :=
  P.cotrip_on x hx

/-- A relevant subdomain: a partial Lambek domain that is cofinal
    for separation — any selfApp overflow can be witnessed within
    the domain.

    The cofinality condition is the key bridge axiom: it says the
    subdomain is "big enough" to carry all complexity-theoretic content.
    Combined with the partial Lambek (selfApp = id on the domain),
    this creates a contradiction with SelfAppUnbounded.

    For Chain 5 (algebraic proofs over GF(2)): the domain is the
    multilinear Boolean fragment. Cofinality holds because the
    Boolean axioms x² - x = 0 let you reduce any polynomial to its
    multilinear representative without increasing degree, and all
    PC refutation steps can be carried out within the fragment. -/
structure RelevantSubdomain (M : GradedReflModel) extends PartialLambekData M where
  /-- Cofinality: if selfApp overflows at grade d anywhere in the carrier,
      it overflows on a domain element at the same or lower grade.

      This says the domain witnesses all separation: you cannot hide
      selfApp overflow outside the partial Lambek domain. -/
  cofinal : ∀ d, (∃ x, M.grade x ≤ d ∧ M.grade (M.selfApp x) > d) →
    (∃ x, domain x ∧ M.grade x ≤ d ∧ M.grade (M.selfApp x) > d)

-- ════════════════════════════════════════════════════════════
-- Section 7: The partial bridge theorem
-- ════════════════════════════════════════════════════════════

/-- PARTIAL BRIDGE THEOREM.

    A relevant subdomain (partial Lambek + cofinality) contradicts
    SelfAppUnbounded. The proof is constructive — no classical logic:

    1. SelfAppUnbounded gives: for every d, there exists x with
       grade(x) ≤ d and grade(selfApp(x)) > d.
    2. Cofinality lifts this to a domain element x' with the same
       overflow property.
    3. Partial Lambek (cotrip_on) gives: selfApp(x') = x' on the domain.
    4. Therefore grade(selfApp(x')) = grade(x') ≤ d.
    5. Contradiction: grade(selfApp(x')) > d and grade(selfApp(x')) ≤ d.

    For Chain 5: this says that IF the multilinear Boolean fragment
    is a relevant subdomain for the algebraic proof complexity model,
    THEN the model cannot have unbounded selfApp — which is exactly
    the bridge condition needed for the lock theorem.

    This is the first chain besides Chain 7 with a formal bridge
    result grounded in the morphism framework. The open condition
    is precisely: prove cofinality of the multilinear Boolean fragment
    (i.e., degree lower bounds can always be witnessed on multilinear
    polynomials). -/
theorem partial_bridge (M : GradedReflModel)
    (R : RelevantSubdomain M) (hub : SelfAppUnbounded M) : False := by
  obtain ⟨x, hxd, hxsa⟩ := hub.overflows 0
  obtain ⟨x', hdom, hxd', hxsa'⟩ := R.cofinal 0 ⟨x, hxd, hxsa⟩
  have heq := R.cotrip_on x' hdom
  simp only [GradedReflModel.selfApp] at hxsa'
  rw [heq] at hxsa'
  omega

end WTS
