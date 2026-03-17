/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/FixedPointClassification.lean — The transport construction satisfies
Group C predicates.

For any GRM M, transportGradedReflModel M has selfApp = id, Compatible
retraction, and PEqNP. This places the transport construction at the
Group C position in the carrier engineering classification.

This file connects the tower (CarrierEngineering) to the transport layer
(TransportSelfSimilarity). It states structural facts about one
construction. It does not connect to the Protocol layer, the lock theorem,
or any chain-specific content.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Tower.CarrierEngineering
import WTS.Transport.TransportSelfSimilarity

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Transport model satisfies Group C predicates
-- ════════════════════════════════════════════════════════════

/-- The transport model's retraction is compatible with its grade.
    Since selfApp = id, grade(selfApp(x)) = grade(x) ≤ grade(x). -/
theorem transport_model_compatible (M : GradedReflModel) :
    (transportGradedReflModel M).toGradedRetraction.Compatible := by
  intro x
  show (transportGradedReflModel M).grade ((transportGradedReflModel M).selfApp x) ≤
       (transportGradedReflModel M).grade x
  rw [transport_model_selfApp_eq_id M x]; exact Nat.le_refl _

/-- The transport model satisfies all Group C predicates:
    compatible retraction, selfApp = id, and PEqNP.
    This holds for ANY GRM M — the meta-level of every model's
    structure-preserving operations satisfies these predicates. -/
theorem transport_model_groupC (M : GradedReflModel) :
    (transportGradedReflModel M).toGradedRetraction.Compatible ∧
    (∀ x, (transportGradedReflModel M).selfApp x = x) ∧
    PEqNP (transportGradedReflModel M) :=
  ⟨transport_model_compatible M,
   transport_model_selfApp_eq_id M,
   transport_model_PEqNP M⟩

-- ════════════════════════════════════════════════════════════
-- Section 2: Transport model in the ULC collection
-- ════════════════════════════════════════════════════════════

/-- The transport model, viewed as a ULC instance, has roundtrip and
    selfApp = id. This places it in the ULC collection at the
    Group C position: roundtrip + selfApp = id. -/
theorem transport_model_ULC (M : GradedReflModel) :
    (transportGradedReflModel M).toULC.HasRoundtrip ∧
    ∀ x, (transportGradedReflModel M).toULC.selfApp x = x :=
  ⟨(transportGradedReflModel M).toULC_hasRoundtrip,
   fun x => by
     rw [(transportGradedReflModel M).toULC_selfApp_eq]
     exact transport_model_selfApp_eq_id M x⟩

end WTS
