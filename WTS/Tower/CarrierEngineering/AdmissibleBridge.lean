/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Tower/CarrierEngineering/AdmissibleBridge.lean — The admissible
classical bridge interface.

Strategic significance: this file closes the gap between the internal
carrier engineering theory (GRM, BoundedGRMEquiv, UnboundedGap,
FiniteDrift) and classical computation semantics. The remaining external
obligation reduces to one question: does the classical semantic target
satisfy these admissibility conditions?

The key insight: we do not need to axiomatize "polynomial time" or
"Turing machines." We need exactly the data that induces a GRM with
bounded grade distortion. An AdmissibleEncoding captures:
  - A carrier type (Names: binary strings, formulas, programs, etc.)
  - fold/unfold: the language-model boundary
  - roundtrip: fold(unfold(x)) = x
  - grade: resource measure (description length, etc.)
  - overhead: bounded additive cost of the encoding

From two admissible encodings of the same domain (SameSemantics),
we derive BoundedGRMEquiv, which transfers all encoding-invariant
properties: UnboundedGap, FiniteDrift, etc.

The encoding-dependence objection is thereby reducible to:
  "does the classical semantic target satisfy admissibility?"

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Tower.CarrierEngineering.ReencodingInvariance

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: The admissible encoding structure
-- ════════════════════════════════════════════════════════════

/-- An admissible encoding of a computation domain into a graded
    reflexive model.

    The key insight: we do not need to axiomatize "polynomial time"
    or "Turing machines." We need exactly the data that induces a GRM
    with bounded grade distortion.

    Names : the carrier type (e.g., binary strings, formulas, programs)
    fold/unfold : the language-model boundary
    roundtrip : fold(unfold(x)) = x
    grade : resource measure (e.g., description length)
    overhead : bounded additive cost of the encoding -/
structure AdmissibleEncoding where
  /-- The carrier type. -/
  Names : Type
  /-- Fold: the encoding direction. -/
  fold : Names → Names
  /-- Unfold: the decoding direction. -/
  unfold : Names → Names
  /-- Roundtrip: fold(unfold(x)) = x. -/
  roundtrip : ∀ x, fold (unfold x) = x
  /-- Resource measure on names. -/
  grade : Names → Nat
  /-- Maximum additive cost of the encoding overhead. -/
  overhead : Nat
  /-- The encoding overhead is bounded:
      grade(unfold(fold(x))) ≤ grade(x) + overhead.
      This is the selfApp boundedness condition. -/
  selfApp_bounded : ∀ x, grade (unfold (fold x)) ≤ grade x + overhead

-- ════════════════════════════════════════════════════════════
-- Section 2: Induced GRM and ReflectiveCarrierData
-- ════════════════════════════════════════════════════════════

/-- Every admissible encoding induces a GradedReflModel. -/
def AdmissibleEncoding.toGRM (E : AdmissibleEncoding) : GradedReflModel where
  carrier := E.Names
  fold := E.fold
  unfold := E.unfold
  roundtrip := E.roundtrip
  grade := E.grade

/-- selfApp on the induced GRM is unfold ∘ fold. -/
theorem AdmissibleEncoding.toGRM_selfApp (E : AdmissibleEncoding) (x : E.Names) :
    E.toGRM.selfApp x = E.unfold (E.fold x) := rfl

/-- Every admissible encoding induces a ReflectiveCarrierData
    (via the induced GRM). -/
def AdmissibleEncoding.toReflectiveCarrierData (E : AdmissibleEncoding) :
    ReflectiveCarrierData :=
  E.toGRM.toReflectiveCarrierData

-- ════════════════════════════════════════════════════════════
-- Section 3: Induced drift extension
-- ════════════════════════════════════════════════════════════

/-- Every admissible encoding admits drift at its overhead parameter.
    The selfApp_bounded condition is exactly what drift_extension_iff
    requires. -/
theorem AdmissibleEncoding.admits_drift (E : AdmissibleEncoding) :
    E.toGRM.AdmitsDrift E.overhead := by
  rw [GradedReflModel.AdmitsDrift, GradedReflModel.drift_extension_iff]
  exact E.selfApp_bounded

-- ════════════════════════════════════════════════════════════
-- Section 4: SameSemantics — the bridge condition
-- ════════════════════════════════════════════════════════════

/-- Two admissible encodings represent the same computation semantics
    when there exist bounded translations between them that commute
    with the fold/unfold structure.

    The translate_compat field is the non-trivial content: it says that
    translation commutes with selfApp. This is what makes the bridge
    non-trivial and enables BoundedGRMEquiv.f_compat. -/
structure SameSemantics (E₁ E₂ : AdmissibleEncoding) where
  /-- Forward translation. -/
  translate : E₁.Names → E₂.Names
  /-- Backward translation. -/
  translate_back : E₂.Names → E₁.Names
  /-- translate_back is left inverse of translate. -/
  translate_roundtrip : ∀ x, translate_back (translate x) = x
  /-- translate is left inverse of translate_back. -/
  translate_roundtrip' : ∀ x, translate (translate_back x) = x
  /-- Maximum additive translation overhead. -/
  translate_overhead : Nat
  /-- Forward translation has bounded grade distortion. -/
  translate_bounded : ∀ x, E₂.grade (translate x) ≤ E₁.grade x + translate_overhead
  /-- Backward translation has bounded grade distortion. -/
  translate_back_bounded : ∀ x, E₁.grade (translate_back x) ≤ E₂.grade x + translate_overhead
  /-- Translation commutes with selfApp.
      This says: translating then canonicalizing in E₂ is the same as
      canonicalizing in E₁ then translating.
      Direction: E₂.selfApp ∘ translate = translate ∘ E₁.selfApp -/
  translate_compat : ∀ x, E₂.unfold (E₂.fold (translate x)) = translate (E₁.unfold (E₁.fold x))

-- ════════════════════════════════════════════════════════════
-- Section 5: THE BRIDGE THEOREM
-- ════════════════════════════════════════════════════════════

/-- THE ADMISSIBLE BRIDGE THEOREM.

    Same-semantics encodings induce a BoundedGRMEquiv between their
    induced GRMs. This is the formal connection between classical
    computation semantics and the carrier engineering obstruction
    theory.

    From this, all encoding-invariance results (UnboundedGap,
    FiniteDrift, fixed-point subdomain equivalence) transfer
    automatically through the existing BoundedGRMEquiv API.

    The overhead of the induced equivalence is the translation
    overhead — not the encoding overhead. The encoding overheads
    are internal to each GRM; the translation overhead measures
    how much the two encodings differ. -/
def SameSemantics.toBoundedGRMEquiv {E₁ E₂ : AdmissibleEncoding}
    (S : SameSemantics E₁ E₂) :
    BoundedGRMEquiv E₁.toGRM E₂.toGRM where
  f := S.translate
  g := S.translate_back
  gf := S.translate_roundtrip
  fg := S.translate_roundtrip'
  overhead := S.translate_overhead
  f_bounded := S.translate_bounded
  g_bounded := S.translate_back_bounded
  f_compat := S.translate_compat

-- ════════════════════════════════════════════════════════════
-- Section 6: Corollaries via existing invariance theorems
-- ════════════════════════════════════════════════════════════

/-- UnboundedGap is invariant across same-semantics encodings. -/
theorem SameSemantics.unboundedGap_iff {E₁ E₂ : AdmissibleEncoding}
    (S : SameSemantics E₁ E₂) :
    E₁.toGRM.UnboundedGap ↔ E₂.toGRM.UnboundedGap :=
  S.toBoundedGRMEquiv.unboundedGap_iff

/-- FiniteDrift existence is invariant across same-semantics encodings. -/
theorem SameSemantics.finiteDrift_iff {E₁ E₂ : AdmissibleEncoding}
    (S : SameSemantics E₁ E₂) :
    E₁.toGRM.FiniteDrift ↔ E₂.toGRM.FiniteDrift :=
  S.toBoundedGRMEquiv.finite_drift_iff

/-- Drift transport (forward): if E₁ admits drift k, then E₂ admits
    drift k + 2 * translate_overhead. -/
theorem SameSemantics.drift_transport {E₁ E₂ : AdmissibleEncoding}
    (S : SameSemantics E₁ E₂) (k : Nat) :
    E₁.toGRM.AdmitsDrift k →
    E₂.toGRM.AdmitsDrift (k + 2 * S.translate_overhead) := by
  intro h
  exact S.toBoundedGRMEquiv.drift_extension_transport k h

/-- Drift transport (backward): if E₂ admits drift k, then E₁ admits
    drift k + 2 * translate_overhead. -/
theorem SameSemantics.drift_transport_back {E₁ E₂ : AdmissibleEncoding}
    (S : SameSemantics E₁ E₂) (k : Nat) :
    E₂.toGRM.AdmitsDrift k →
    E₁.toGRM.AdmitsDrift (k + 2 * S.translate_overhead) := by
  intro h
  exact S.toBoundedGRMEquiv.drift_extension_transport_g k h

-- ════════════════════════════════════════════════════════════
-- Section 7: The identity encoding
-- ════════════════════════════════════════════════════════════

/-- Every GRM is an admissible encoding of itself.
    The identity encoding has the same fold/unfold and grade, with
    overhead determined by the GRM's own selfApp growth.

    For this to work, we need a global bound on selfApp growth.
    We parametrize by the overhead. -/
def GradedReflModel.toAdmissibleEncoding (M : GradedReflModel)
    (k : Nat) (h : ∀ x, M.grade (M.selfApp x) ≤ M.grade x + k) :
    AdmissibleEncoding where
  Names := M.carrier
  fold := M.fold
  unfold := M.unfold
  roundtrip := M.roundtrip
  grade := M.grade
  overhead := k
  selfApp_bounded := h

/-- The identity encoding induces the same GRM (definitionally). -/
theorem GradedReflModel.toAdmissibleEncoding_toGRM (M : GradedReflModel)
    (k : Nat) (h : ∀ x, M.grade (M.selfApp x) ≤ M.grade x + k) :
    (M.toAdmissibleEncoding k h).toGRM = M := by
  rfl

-- ════════════════════════════════════════════════════════════
-- Section 8: Protocol connection
-- ════════════════════════════════════════════════════════════

/-- Every ProtocolGRM yields an AdmissibleEncoding.
    The overhead is 2 * transportOverhead, the standard protocol
    bound from selfApp_constant_overhead. -/
def ProtocolGRM.toAdmissibleEncoding (P : ProtocolGRM) :
    AdmissibleEncoding where
  Names := P.sys.State
  fold := P.encode
  unfold := P.decode
  roundtrip := P.h_roundtrip
  grade := P.sys.cost
  overhead := 2 * P.sys.transportOverhead
  selfApp_bounded := P.selfApp_constant_overhead

/-- The protocol-induced AdmissibleEncoding induces the same GRM
    as the protocol. -/
theorem ProtocolGRM.toAdmissibleEncoding_toGRM (P : ProtocolGRM) :
    P.toAdmissibleEncoding.toGRM = P.toGRM := by
  rfl

/-- Every ProtocolGRM admits drift via the admissible encoding path. -/
theorem ProtocolGRM.admits_drift_via_bridge (P : ProtocolGRM) :
    P.toAdmissibleEncoding.toGRM.AdmitsDrift (2 * P.sys.transportOverhead) :=
  P.toAdmissibleEncoding.admits_drift

-- ════════════════════════════════════════════════════════════
-- Section 9: Composability — SameSemantics is reflexive and symmetric
-- ════════════════════════════════════════════════════════════

/-- SameSemantics is reflexive: every encoding has the same semantics
    as itself, via the identity translation. -/
def SameSemantics.refl (E : AdmissibleEncoding) : SameSemantics E E where
  translate := id
  translate_back := id
  translate_roundtrip _ := rfl
  translate_roundtrip' _ := rfl
  translate_overhead := 0
  translate_bounded x := by simp [id]
  translate_back_bounded x := by simp [id]
  translate_compat _ := rfl

/-- SameSemantics is symmetric: if E₁ has the same semantics as E₂,
    then E₂ has the same semantics as E₁. -/
def SameSemantics.symm {E₁ E₂ : AdmissibleEncoding}
    (S : SameSemantics E₁ E₂) : SameSemantics E₂ E₁ where
  translate := S.translate_back
  translate_back := S.translate
  translate_roundtrip := S.translate_roundtrip'
  translate_roundtrip' := S.translate_roundtrip
  translate_overhead := S.translate_overhead
  translate_bounded := S.translate_back_bounded
  translate_back_bounded := S.translate_bounded
  translate_compat x := by
    -- Need: E₁.unfold (E₁.fold (S.translate_back x)) =
    --       S.translate_back (E₂.unfold (E₂.fold x))
    -- From translate_compat at translate_back(x):
    --   E₂.unfold (E₂.fold (S.translate (S.translate_back x)))
    --     = S.translate (E₁.unfold (E₁.fold (S.translate_back x)))
    -- By translate_roundtrip':
    --   E₂.unfold (E₂.fold x) = S.translate (E₁.unfold (E₁.fold (S.translate_back x)))
    -- Apply translate_back:
    --   S.translate_back (E₂.unfold (E₂.fold x))
    --     = S.translate_back (S.translate (E₁.unfold (E₁.fold (S.translate_back x))))
    --     = E₁.unfold (E₁.fold (S.translate_back x))
    have h := S.translate_compat (S.translate_back x)
    rw [S.translate_roundtrip'] at h
    -- h : E₂.unfold (E₂.fold x) = S.translate (E₁.unfold (E₁.fold (S.translate_back x)))
    have h2 : S.translate_back (E₂.unfold (E₂.fold x)) =
        S.translate_back (S.translate (E₁.unfold (E₁.fold (S.translate_back x)))) :=
      congrArg S.translate_back h
    rw [S.translate_roundtrip] at h2
    exact h2.symm

/-- SameSemantics is transitive: composing translations. -/
def SameSemantics.trans {E₁ E₂ E₃ : AdmissibleEncoding}
    (S₁₂ : SameSemantics E₁ E₂) (S₂₃ : SameSemantics E₂ E₃) :
    SameSemantics E₁ E₃ where
  translate := S₂₃.translate ∘ S₁₂.translate
  translate_back := S₁₂.translate_back ∘ S₂₃.translate_back
  translate_roundtrip x := by
    show S₁₂.translate_back (S₂₃.translate_back (S₂₃.translate (S₁₂.translate x))) = x
    rw [S₂₃.translate_roundtrip, S₁₂.translate_roundtrip]
  translate_roundtrip' x := by
    show S₂₃.translate (S₁₂.translate (S₁₂.translate_back (S₂₃.translate_back x))) = x
    rw [S₁₂.translate_roundtrip', S₂₃.translate_roundtrip']
  translate_overhead := S₁₂.translate_overhead + S₂₃.translate_overhead
  translate_bounded x := by
    show E₃.grade (S₂₃.translate (S₁₂.translate x)) ≤
         E₁.grade x + (S₁₂.translate_overhead + S₂₃.translate_overhead)
    have h1 := S₁₂.translate_bounded x
    have h2 := S₂₃.translate_bounded (S₁₂.translate x)
    omega
  translate_back_bounded x := by
    show E₁.grade (S₁₂.translate_back (S₂₃.translate_back x)) ≤
         E₃.grade x + (S₁₂.translate_overhead + S₂₃.translate_overhead)
    have h1 := S₂₃.translate_back_bounded x
    have h2 := S₁₂.translate_back_bounded (S₂₃.translate_back x)
    omega
  translate_compat x := by
    -- Need: E₃.selfApp (S₂₃.translate (S₁₂.translate x))
    --     = S₂₃.translate (S₁₂.translate (E₁.selfApp x))
    -- By S₁₂.translate_compat: E₂.selfApp (S₁₂.translate x) = S₁₂.translate (E₁.selfApp x)
    -- By S₂₃.translate_compat: E₃.selfApp (S₂₃.translate y) = S₂₃.translate (E₂.selfApp y)
    show E₃.unfold (E₃.fold (S₂₃.translate (S₁₂.translate x))) =
         S₂₃.translate (S₁₂.translate (E₁.unfold (E₁.fold x)))
    rw [S₂₃.translate_compat (S₁₂.translate x)]
    rw [S₁₂.translate_compat x]

-- ════════════════════════════════════════════════════════════
-- Section 10: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms AdmissibleEncoding.toGRM
#print axioms AdmissibleEncoding.toGRM_selfApp
#print axioms AdmissibleEncoding.toReflectiveCarrierData
#print axioms AdmissibleEncoding.admits_drift
#print axioms SameSemantics.toBoundedGRMEquiv
#print axioms SameSemantics.unboundedGap_iff
#print axioms SameSemantics.finiteDrift_iff
#print axioms SameSemantics.drift_transport
#print axioms SameSemantics.drift_transport_back
#print axioms GradedReflModel.toAdmissibleEncoding
#print axioms GradedReflModel.toAdmissibleEncoding_toGRM
#print axioms ProtocolGRM.toAdmissibleEncoding
#print axioms ProtocolGRM.toAdmissibleEncoding_toGRM
#print axioms ProtocolGRM.admits_drift_via_bridge
#print axioms SameSemantics.refl
#print axioms SameSemantics.symm
#print axioms SameSemantics.trans

end WTS
