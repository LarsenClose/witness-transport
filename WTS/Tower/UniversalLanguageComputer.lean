/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/UniversalLanguageComputer.lean — The space of language × computational model pairings.

The minimal universal: two types and two maps between them.
selfApp = decode ∘ encode. With roundtrip, selfApp is idempotent.
Without roundtrip, idempotence can fail.

This is a standalone object. It does not import or extend GradedReflModel.

STATUS: 0 sorry.
-/

namespace WTS

/-- A language × computational model pairing.
    Two types and two maps between them. No roundtrip assumed. -/
structure UniversalLanguageComputer where
  Lang : Type
  CompModel : Type
  encode : Lang → CompModel
  decode : CompModel → Lang

/-- The residual of the round-trip: decode ∘ encode. -/
def UniversalLanguageComputer.selfApp (P : UniversalLanguageComputer) (x : P.Lang) : P.Lang :=
  P.decode (P.encode x)

/-- Roundtrip: encode ∘ decode = id on the model side. -/
def UniversalLanguageComputer.HasRoundtrip (P : UniversalLanguageComputer) : Prop :=
  ∀ y : P.CompModel, P.encode (P.decode y) = y

/-- Roundtrip implies selfApp is idempotent.
    selfApp(selfApp(x)) = decode(encode(decode(encode(x))))
                         = decode(encode(x))      — by roundtrip on encode(x)
                         = selfApp(x) -/
theorem UniversalLanguageComputer.roundtrip_selfApp_idempotent (P : UniversalLanguageComputer)
    (h : P.HasRoundtrip) :
    ∀ x, P.selfApp (P.selfApp x) = P.selfApp x := by
  intro x
  show P.decode (P.encode (P.decode (P.encode x))) = P.decode (P.encode x)
  rw [h (P.encode x)]

/-- The language=model fixed point: Lang = CompModel, encode = decode = id.
    Has roundtrip, and selfApp = id. -/
def unifiedPairing (α : Type) : UniversalLanguageComputer where
  Lang := α
  CompModel := α
  encode := id
  decode := id

theorem unified_hasRoundtrip_and_selfApp_eq_id (α : Type) :
    (unifiedPairing α).HasRoundtrip ∧ ∀ x, (unifiedPairing α).selfApp x = x :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- Without roundtrip, idempotence can fail. -/
theorem exists_non_idempotent :
    ∃ P : UniversalLanguageComputer,
      ¬P.HasRoundtrip ∧ ∃ x, P.selfApp (P.selfApp x) ≠ P.selfApp x := by
  refine ⟨⟨Nat, Nat, (· + 1), (· + 1)⟩, ?_, 0, ?_⟩
  · intro h; have := h (0 : Nat); simp at this
  · simp [UniversalLanguageComputer.selfApp]

end WTS
