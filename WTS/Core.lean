/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Core.lean — Foundation definitions for the witness transport calculus.

STATUS: 0 sorry, 0 Classical.choice.
-/

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: The central structure
-- ════════════════════════════════════════════════════════════

structure GradedReflModel where
  carrier : Type
  fold : carrier → carrier
  unfold : carrier → carrier
  roundtrip : ∀ x, fold (unfold x) = x
  grade : carrier → Nat

def GradedReflModel.selfApp (M : GradedReflModel) (x : M.carrier) : M.carrier :=
  M.unfold (M.fold x)

-- CRITICAL: direct form, NOT existential. Verified across all 16 copies.
def FactorsThrough (M : GradedReflModel) (f : M.carrier → M.carrier) (d : Nat) : Prop :=
  ∀ x, M.grade x ≤ d → M.grade (f x) ≤ d

structure SelfAppUnbounded (M : GradedReflModel) where
  -- Field name: `overflows` (14-file majority, not `overflows_all`)
  overflows : ∀ d, ∃ x, M.grade x ≤ d ∧ M.grade (M.selfApp x) > d

structure TuringComplete (M : GradedReflModel) where
  unbounded_elements : ∀ K, ∃ x, M.grade x > K
  selfApp_unbounded : SelfAppUnbounded M

def PEqNP (M : GradedReflModel) : Prop :=
  ∃ d, FactorsThrough M M.selfApp d

-- ════════════════════════════════════════════════════════════
-- Section 2: Growth gap
-- ════════════════════════════════════════════════════════════

def HasGrowthGap (N_End N_L : Nat → Nat) (overhead : Nat) : Prop :=
  ∃ g, N_End g > N_L (g + overhead)

-- ════════════════════════════════════════════════════════════
-- Section 3: Polynomial bounds
-- ════════════════════════════════════════════════════════════

structure PolyBound where
  degree : Nat
  constant : Nat

def PolyBound.eval (p : PolyBound) (n : Nat) : Nat :=
  n ^ p.degree + p.constant

-- ════════════════════════════════════════════════════════════
-- Section 3b: Abstract computation model
-- ════════════════════════════════════════════════════════════

/-- Abstract computation model for complexity.
    Step-bounded evaluation with monotonicity. -/
structure CompModel where
  /-- Type of programs. -/
  Prog : Type
  /-- Run program p on input x for at most t steps, returning output or none. -/
  run : Prog → Nat → Nat → Option Nat
  /-- Monotonicity: if a computation halts in t steps, it halts in t' ≥ t steps
      with the same result. -/
  mono : ∀ p x t t' v, run p x t = some v → t ≤ t' → run p x t' = some v

/-- Alias: CompModelPoly = CompModel. -/
abbrev CompModelPoly := CompModel

-- ════════════════════════════════════════════════════════════
-- Section 4: Utility lemmas (duplicated 13-16 times each)
-- ════════════════════════════════════════════════════════════

theorem gt_le_absurd {a b : Nat} (hgt : a > b) (hle : a ≤ b) : False :=
  Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hgt hle)

theorem two_pow_succ_gt (n : Nat) : 2 ^ (n + 1) > 2 ^ n := by
  have : 2 ^ n ≥ 1 := Nat.one_le_pow n 2 (by omega)
  rw [Nat.pow_succ]; omega

/-- 2^m < 2^n when m < n. -/
theorem two_pow_strict_mono {m n : Nat} (h : m < n) : 2 ^ m < 2 ^ n := by
  induction h with
  | refl => exact two_pow_succ_gt m
  | step _ ih => exact Nat.lt_trans ih (two_pow_succ_gt _)

/-- 2^m ≤ 2^n when m ≤ n. -/
theorem two_pow_mono {m n : Nat} (h : m ≤ n) : 2 ^ m ≤ 2 ^ n :=
  Nat.pow_le_pow_right (by omega : 0 < 2) h

/-- 2^(n+1) ≥ 2 for all n. -/
theorem two_pow_ge_2 (n : Nat) : 2 ^ (n + 1) ≥ 2 :=
  Nat.le_trans (Nat.le_refl 2)
    (Nat.pow_le_pow_right (by omega : 2 > 0) (by omega : 1 ≤ n + 1))

/-- For a ≥ 2, a^a ≥ 2^a. -/
theorem pow_self_ge_two_pow (a : Nat) (ha : a ≥ 2) : a ^ a ≥ 2 ^ a :=
  Nat.pow_le_pow_left ha a

/-- 2^n > n for all n. -/
theorem two_pow_gt_n : ∀ n, 2 ^ n > n := by
  intro n
  induction n with
  | zero => decide
  | succ k ih =>
    have : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
    have : 2 ^ k ≥ 1 := Nat.one_le_two_pow
    omega

/-- 2^n ≥ n + 1. -/
theorem two_pow_ge_succ (n : Nat) : 2 ^ n ≥ n + 1 := two_pow_gt_n n

/-- For n ≥ 2, n^n ≥ n^2. -/
theorem pow_self_ge_sq (n : Nat) (hn : n ≥ 2) : n ^ n ≥ n ^ 2 :=
  Nat.pow_le_pow_right (by omega : 0 < n) hn

/-- 2^m ≥ m * m for m ≥ 4. -/
theorem two_pow_ge_sq (m : Nat) (hm : m ≥ 4) : 2 ^ m ≥ m * m := by
  induction m with
  | zero => omega
  | succ k ih =>
    match Nat.lt_or_ge k 4 with
    | Or.inl hk =>
      have : k = 3 := by omega
      subst this; decide
    | Or.inr hk =>
      have ihk := ih hk
      have h_pow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
      have h_expand : (k + 1) * (k + 1) = k * k + k + k + 1 := by
        rw [Nat.succ_mul, Nat.mul_succ]; omega
      rw [h_pow, h_expand]
      have h1 : 2 ^ k * 2 ≥ k * k * 2 := Nat.mul_le_mul_right 2 ihk
      have h_kk : k * k ≥ 4 * k := Nat.mul_le_mul_right k hk
      omega

-- ════════════════════════════════════════════════════════════
-- Section 5: Shared theorems (proved once, used everywhere)
-- ════════════════════════════════════════════════════════════

/-- Verification (fold ∘ unfold) factors through every grade. -/
theorem verification_factors (M : GradedReflModel) (d : Nat) :
    FactorsThrough M (fun x => M.fold (M.unfold x)) d := by
  intro x hx; dsimp only; rw [M.roundtrip]; exact hx

/-- selfApp does not factor through any grade when unbounded. -/
theorem selfApp_not_factors (M : GradedReflModel) (h : SelfAppUnbounded M) (d : Nat) :
    ¬FactorsThrough M M.selfApp d := by
  intro hf; obtain ⟨x, hle, hgt⟩ := h.overflows d; have := hf x hle; omega

/-- Verification ≠ solving when selfApp is unbounded. -/
theorem verification_ne_solving (M : GradedReflModel) (h : SelfAppUnbounded M) :
    (fun x => M.fold (M.unfold x)) ≠ M.selfApp := by
  intro heq
  have habs := selfApp_not_factors M h 0
  apply habs; intro x hx
  have hfold : M.grade (M.fold (M.unfold x)) ≤ 0 := by rw [M.roundtrip]; exact hx
  have heqx := congrFun heq x
  rw [heqx] at hfold; exact hfold

/-- Turing completeness implies separation. -/
theorem from_turing_complete (M : GradedReflModel) (tc : TuringComplete M) :
    (fun x => M.fold (M.unfold x)) ≠ M.selfApp :=
  verification_ne_solving M tc.selfApp_unbounded

-- ════════════════════════════════════════════════════════════
-- Section 6: Concrete models (built once, used everywhere)
-- ════════════════════════════════════════════════════════════

/-- Trivial model: Unit carrier, id fold/unfold, grade 0. P = NP here. -/
def trivialModel : GradedReflModel where
  carrier := Unit; fold := id; unfold := id
  roundtrip _ := rfl; grade _ := 0

/-- Grade function for the standard model. -/
private def overflowGrade (x : Nat) : Nat :=
  if x % 2 == 0 then 0 else (x + 1) / 2

/-- Standard model: Nat carrier, fold = /2, unfold = 2x+1. P ≠ NP here. -/
def standardModel : GradedReflModel where
  carrier := Nat; fold x := x / 2; unfold x := 2 * x + 1
  roundtrip x := by show (2 * x + 1) / 2 = x; omega
  grade := overflowGrade

theorem overflowGrade_even (k : Nat) : overflowGrade (2 * k) = 0 := by
  unfold overflowGrade; have h : (2 * k) % 2 = 0 := by omega
  have : ((2 * k) % 2 == 0) = true := by rw [h]; rfl
  rw [if_pos (by exact this)]

theorem overflowGrade_odd (k : Nat) : overflowGrade (2 * k + 1) = k + 1 := by
  unfold overflowGrade; have h : (2 * k + 1) % 2 = 1 := by omega
  have : ((2 * k + 1) % 2 == 0) = false := by rw [h]; rfl
  rw [if_neg (by exact Bool.eq_false_iff.mp this)]; omega

theorem standardModel_overflow (d : Nat) :
    standardModel.grade (2 * d) ≤ d ∧
    standardModel.grade (standardModel.selfApp (2 * d)) > d := by
  constructor
  · show overflowGrade (2 * d) ≤ d; rw [overflowGrade_even]; omega
  · show overflowGrade (2 * (2 * d / 2) + 1) > d
    have : 2 * d / 2 = d := by omega
    rw [this, overflowGrade_odd]; omega

def standardModel_selfAppUnbounded : SelfAppUnbounded standardModel where
  overflows d := ⟨2 * d, standardModel_overflow d⟩

def standardModel_turingComplete : TuringComplete standardModel where
  unbounded_elements K := ⟨2 * K + 3, by
    show overflowGrade (2 * K + 3) > K
    have h : (2 * K + 3) % 2 = 1 := by omega
    unfold overflowGrade
    have : ((2 * K + 3) % 2 == 0) = false := by rw [h]; rfl
    rw [if_neg (by exact Bool.eq_false_iff.mp this)]; omega⟩
  selfApp_unbounded := standardModel_selfAppUnbounded

/-- Conservativity: both regimes exist. -/
theorem conservativity :
    (∃ M : GradedReflModel, ∀ x, M.selfApp x = x) ∧
    (∃ M : GradedReflModel, SelfAppUnbounded M) :=
  ⟨⟨trivialModel, fun x => by cases x; rfl⟩,
   ⟨standardModel, standardModel_selfAppUnbounded⟩⟩

-- ════════════════════════════════════════════════════════════
-- Section 7: Counting functions (N_Val, N_End) and binary models
-- ════════════════════════════════════════════════════════════

/-! ## Binary value and endomorphism counting

Values are binary strings of length at most g: N_Val(g) = 2^(g+1).
Endomorphisms are total functions from g-bit values to g-bit values:
N_End(g) = N_Val(g)^N_Val(g). -/

/-- Number of distinct values with binary description length <= g. -/
def N_Val (g : Nat) : Nat := 2 ^ (g + 1)

/-- Number of distinct endomorphisms on g-bit values. -/
def N_End (g : Nat) : Nat := N_Val g ^ N_Val g

/-- N_Val is positive: 2^(g+1) > 0. -/
theorem N_Val_pos (g : Nat) : N_Val g > 0 :=
  Nat.two_pow_pos (g + 1)

/-- N_Val is at least 2 for all g. -/
theorem N_Val_ge_2 (g : Nat) : N_Val g ≥ 2 := by
  unfold N_Val
  have : g + 1 ≥ 1 := by omega
  calc 2 ^ (g + 1) ≥ 2 ^ 1 := Nat.pow_le_pow_right (by omega) this
    _ = 2 := by omega

/-- N_Val is monotone (general form). -/
theorem N_Val_mono {g₁ g₂ : Nat} (h : g₁ ≤ g₂) : N_Val g₁ ≤ N_Val g₂ := by
  unfold N_Val
  exact Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)

/-- N_Val is monotone (successor form). -/
theorem N_Val_mono_succ (g : Nat) : N_Val g ≤ N_Val (g + 1) :=
  N_Val_mono (Nat.le_succ g)

-- ════════════════════════════════════════════════════════════
-- Section 8: Binary model structures
-- ════════════════════════════════════════════════════════════

/-- A binary standard model: programs graded over binary-encoded values. -/
structure BinaryModel where
  /-- Count of programs in slice <= g. -/
  NProg : Nat → Nat
  /-- Monotonicity of program counts. -/
  NProg_mono : ∀ g, NProg g ≤ NProg (g + 1)
  /-- Overhead function. -/
  rho : Nat → Nat
  /-- rho is monotone. -/
  rho_mono : ∀ g, rho g ≤ rho (g + 1)
  /-- Table representability: NProg(rho(g)) >= NVal(g)^NVal(g). -/
  table_count : ∀ g, NProg (rho g) ≥ N_Val g ^ N_Val g

/-- A binary model with linear overhead: rho(g) <= a*g + b. -/
structure LinearBinaryModel extends BinaryModel where
  /-- Linear overhead coefficient. -/
  rho_coeff : Nat
  /-- Linear overhead constant. -/
  rho_const : Nat
  /-- rho(g) is bounded linearly. -/
  rho_linear : ∀ g, rho g ≤ rho_coeff * g + rho_const

/-- Abstract grade structure on an endomorphism algebra and carrier. -/
structure GradeStructure where
  /-- Cumulative count of endomorphisms with grade <= g. -/
  N_End : Nat → Nat
  /-- Cumulative count of carrier elements with grade <= g. -/
  N_L : Nat → Nat
  /-- Monotonicity: cumulative counts are non-decreasing. -/
  N_End_mono : ∀ g, N_End g ≤ N_End (g + 1)
  N_L_mono : ∀ g, N_L g ≤ N_L (g + 1)

/-- trivialModel.selfApp = id (pointwise form). -/
theorem trivial_selfApp_eq_id : ∀ x, trivialModel.selfApp x = x := by
  intro x; cases x; rfl

end WTS
