/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Protocol/ProtocolGRMBridge.lean — The bridge from distributed witness
systems to graded reflexive models.

A ProtocolGRM is a DWS equipped with a language-model pairing: two agents
whose transport operations serve as fold/unfold. The induced endomorphism
decode ∘ encode is idempotent by roundtrip, so every ProtocolGRM yields
canonical ReflectiveCarrierData constructively.

General bound: selfApp increases grade by at most 2 * transportOverhead
(additive control). This does NOT give FactorsThrough unless overhead = 0.

Collapse corners:
  - HasCotrip gives selfApp = id, gradeGap = 0, hence Group C.
  - Zero transportOverhead rules out SelfAppUnbounded and yields PEqNP.

Open: for positive transportOverhead, ProtocolGRM gives bounded additive
selfApp growth, but whether the protocol structure further constrains
SelfAppUnbounded remains open.

Coherence: max coherence on encode/decode gives step-level consequence
closure. This is separate from the gradeGap collapse, which comes from
cotrip, not from coherence.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Protocol.CoherenceTransportMeasure
import WTS.ReturnPath.Naming.GradeGapMeasure
import WTS.Tower.CarrierEngineering

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: The ProtocolGRM structure
-- ════════════════════════════════════════════════════════════

/-- A protocol-level GRM: a distributed witness system with a
    language-model pairing given by transport between two agents.

    The two agents form the language-model boundary:
    - lang_agent: the "language" side (expressions, formulas, programs)
    - model_agent: the "model" side (computations, semantics, witnesses)
    - encode: transport from language to model (fold)
    - decode: transport from model to language (unfold)
    - roundtrip: encode(decode(x)) = x (fold(unfold(x)) = x)

    The roundtrip axiom corresponds to: encoding a decoded value
    recovers the original. This is the GRM roundtrip.

    The COTRIP (decode(encode(x)) = x) is the open condition.
    When it holds, selfApp = id and gradeGap = 0 (Group C). -/
structure ProtocolGRM where
  /-- The underlying distributed witness system -/
  sys : DistributedWitnessSystem
  /-- The language agent -/
  lang_agent : sys.AgentType
  /-- The model agent -/
  model_agent : sys.AgentType
  /-- Encode: transport from language to model (fold) -/
  encode : sys.State → sys.State
  /-- Decode: transport from model to language (unfold) -/
  decode : sys.State → sys.State
  /-- Encode is a valid transport -/
  h_encode_transport : ∀ s, sys.transport lang_agent model_agent s (encode s)
  /-- Decode is a valid transport -/
  h_decode_transport : ∀ s, sys.transport model_agent lang_agent s (decode s)
  /-- Roundtrip: encode after decode is identity -/
  h_roundtrip : ∀ s, encode (decode s) = s

-- ════════════════════════════════════════════════════════════
-- Section 2: The induced GRM
-- ════════════════════════════════════════════════════════════

/-- The GRM induced by a protocol-level language-model pairing.
    carrier = State, fold = encode, unfold = decode, grade = cost. -/
def ProtocolGRM.toGRM (P : ProtocolGRM) : GradedReflModel where
  carrier := P.sys.State
  fold := P.encode
  unfold := P.decode
  roundtrip := P.h_roundtrip
  grade := P.sys.cost

/-- selfApp on the induced GRM is decode ∘ encode. -/
theorem ProtocolGRM.selfApp_eq (P : ProtocolGRM) (s : P.sys.State) :
    P.toGRM.selfApp s = P.decode (P.encode s) := rfl

-- ════════════════════════════════════════════════════════════
-- Section 3: The cotrip condition and Group C
-- ════════════════════════════════════════════════════════════

/-- The cotrip condition: decode(encode(x)) = x for all states.
    This is the open condition for Chain 7. When it holds,
    transport in both directions is invertible — language and
    model are the same thing. -/
def ProtocolGRM.HasCotrip (P : ProtocolGRM) : Prop :=
  ∀ s, P.decode (P.encode s) = s

/-- Cotrip implies selfApp = id on the induced GRM. -/
theorem ProtocolGRM.cotrip_selfApp_eq_id (P : ProtocolGRM)
    (h : P.HasCotrip) :
    ∀ x, P.toGRM.selfApp x = x :=
  h

/-- Cotrip implies gradeGap = 0 everywhere on the induced GRM. -/
theorem ProtocolGRM.cotrip_zero_gap (P : ProtocolGRM)
    (h : P.HasCotrip) :
    ∀ x, gradeGap P.toGRM x = 0 := by
  intro x
  simp only [gradeGap, GradedReflModel.selfApp, ProtocolGRM.toGRM]
  have := h x
  rw [this]; omega

/-- Cotrip implies Compatible (gradeGap ≤ 0). -/
theorem ProtocolGRM.cotrip_compatible (P : ProtocolGRM)
    (h : P.HasCotrip) :
    P.toGRM.toGradedRetraction.Compatible := by
  rw [(compatible_iff_nonpositive_gap P.toGRM)]
  intro x
  have := P.cotrip_zero_gap h x
  omega

/-- Cotrip implies PEqNP on the induced GRM. -/
theorem ProtocolGRM.cotrip_PEqNP (P : ProtocolGRM)
    (h : P.HasCotrip) :
    PEqNP P.toGRM :=
  compatible_retraction_gives_PEqNP P.toGRM (P.cotrip_compatible h)

/-- The full Group C package from cotrip. -/
theorem ProtocolGRM.cotrip_groupC (P : ProtocolGRM)
    (h : P.HasCotrip) :
    (∀ x, P.toGRM.selfApp x = x) ∧
    (∀ x, gradeGap P.toGRM x = 0) ∧
    P.toGRM.toGradedRetraction.Compatible ∧
    PEqNP P.toGRM :=
  ⟨P.cotrip_selfApp_eq_id h,
   P.cotrip_zero_gap h,
   P.cotrip_compatible h,
   P.cotrip_PEqNP h⟩

-- ════════════════════════════════════════════════════════════
-- Section 4: Coherence connection
-- ════════════════════════════════════════════════════════════

/-- Step-level consequence closure for encode: max coherence on the
    encode step means the language-to-model transport preserves
    realizability at bounded cost. -/
def ProtocolGRM.encodeConsequenceClosed (P : ProtocolGRM) : Prop :=
  ∀ s d, P.sys.cost s ≤ d → P.sys.realize P.lang_agent s →
    P.sys.cost (P.encode s) ≤ d + P.sys.transportOverhead ∧
    P.sys.realize P.model_agent (P.encode s)

/-- Step-level consequence closure for decode: max coherence on the
    decode step means the model-to-language transport preserves
    realizability at bounded cost. -/
def ProtocolGRM.decodeConsequenceClosed (P : ProtocolGRM) : Prop :=
  ∀ s d, P.sys.cost s ≤ d → P.sys.realize P.model_agent s →
    P.sys.cost (P.decode s) ≤ d + P.sys.transportOverhead ∧
    P.sys.realize P.lang_agent (P.decode s)

/-- Max coherence on encode implies encodeConsequenceClosed. -/
theorem ProtocolGRM.max_coherence_encode (P : ProtocolGRM)
    (cm : CoherenceMeasure P.sys)
    (h_max : ∀ s, cm.measure_step P.lang_agent P.model_agent
      s (P.encode s) = cm.max_coherence) :
    P.encodeConsequenceClosed := by
  intro s d hcost hreal
  have htrans := P.h_encode_transport s
  have hclosed := (cm.h_full_iff_closed P.lang_agent P.model_agent
    s (P.encode s) htrans).mp (h_max s)
  exact hclosed d hcost hreal

/-- Max coherence on decode implies decodeConsequenceClosed. -/
theorem ProtocolGRM.max_coherence_decode (P : ProtocolGRM)
    (cm : CoherenceMeasure P.sys)
    (h_max : ∀ s, cm.measure_step P.model_agent P.lang_agent
      s (P.decode s) = cm.max_coherence) :
    P.decodeConsequenceClosed := by
  intro s d hcost hreal
  have htrans := P.h_decode_transport s
  have hclosed := (cm.h_full_iff_closed P.model_agent P.lang_agent
    s (P.decode s) htrans).mp (h_max s)
  exact hclosed d hcost hreal

-- ════════════════════════════════════════════════════════════
-- Section 5: The full coherence-gradeGap bridge
-- ════════════════════════════════════════════════════════════

/-- THE COHERENCE-GRADEGAP BRIDGE.

    Given a ProtocolGRM with both roundtrips (cotrip), max coherence
    on both transport directions implies:
    (1) Both transports are consequence-closed
    (2) selfApp = id on the induced GRM
    (3) gradeGap = 0 everywhere
    (4) The induced GRM is Group C

    The coherence hypotheses give step-level consequence closure.
    The gradeGap = 0 and Group C properties come from the cotrip
    hypothesis, not from coherence. These are two independent
    facts bundled together: coherence → closure, cotrip → collapse.

    The cotrip hypothesis (HasCotrip) is the open condition for
    Chain 7. -/
theorem coherence_gradeGap_bridge (P : ProtocolGRM)
    (h_cotrip : P.HasCotrip)
    (cm : CoherenceMeasure P.sys)
    (h_coh_encode : ∀ s, cm.measure_step P.lang_agent P.model_agent
      s (P.encode s) = cm.max_coherence)
    (h_coh_decode : ∀ s, cm.measure_step P.model_agent P.lang_agent
      s (P.decode s) = cm.max_coherence) :
    -- Consequence closure at protocol level
    P.encodeConsequenceClosed ∧
    P.decodeConsequenceClosed ∧
    -- Group C at GRM level
    (∀ x, P.toGRM.selfApp x = x) ∧
    (∀ x, gradeGap P.toGRM x = 0) ∧
    P.toGRM.toGradedRetraction.Compatible ∧
    PEqNP P.toGRM :=
  ⟨P.max_coherence_encode cm h_coh_encode,
   P.max_coherence_decode cm h_coh_decode,
   P.cotrip_selfApp_eq_id h_cotrip,
   P.cotrip_zero_gap h_cotrip,
   P.cotrip_compatible h_cotrip,
   P.cotrip_PEqNP h_cotrip⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: Without cotrip — the general case
-- ════════════════════════════════════════════════════════════

/-- Without cotrip, the ProtocolGRM still induces a valid GRM
    (roundtrip holds), but selfApp = decode ∘ encode may not be
    identity. The gradeGap measures how far the protocol is from
    the Group C condition.

    gradeGap(P, s) = cost(decode(encode(s))) - cost(s)

    This is the protocol-level carrier engineering gap: how much
    cost the language-model roundtrip adds at each state. -/
theorem protocol_gradeGap_is_roundtrip_cost (P : ProtocolGRM)
    (s : P.sys.State) :
    gradeGap P.toGRM s =
      (P.sys.cost (P.decode (P.encode s)) : Int) - (P.sys.cost s : Int) := by
  rfl

/-- Transport cost bound gives an upper bound on gradeGap.
    Each direction adds at most transportOverhead, so the roundtrip
    adds at most 2 * transportOverhead. -/
theorem protocol_gradeGap_bounded (P : ProtocolGRM) (s : P.sys.State) :
    gradeGap P.toGRM s ≤ 2 * P.sys.transportOverhead := by
  simp only [gradeGap, GradedReflModel.selfApp, ProtocolGRM.toGRM]
  have h1 := P.sys.h_transport_cost P.lang_agent P.model_agent
    s (P.encode s) (P.h_encode_transport s)
  have h2 := P.sys.h_transport_cost P.model_agent P.lang_agent
    (P.encode s) (P.decode (P.encode s)) (P.h_decode_transport (P.encode s))
  omega

-- ════════════════════════════════════════════════════════════
-- Section 7: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms ProtocolGRM.cotrip_selfApp_eq_id
#print axioms ProtocolGRM.cotrip_zero_gap
#print axioms ProtocolGRM.cotrip_compatible
#print axioms ProtocolGRM.cotrip_PEqNP
#print axioms ProtocolGRM.cotrip_groupC
#print axioms ProtocolGRM.max_coherence_encode
#print axioms ProtocolGRM.max_coherence_decode
#print axioms coherence_gradeGap_bridge
#print axioms protocol_gradeGap_is_roundtrip_cost
#print axioms protocol_gradeGap_bounded

end WTS
