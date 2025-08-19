import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: Nat → Nat → Nat → Bool)
-- inputs
(a b c: Nat) :=
-- spec
let spec (result: Bool) :=
result ↔
  0 < a ∧ 0 < b ∧ 0 < c ∧
  ((a * a + b * b = c * c) ∨
  (a * a + c * c = b * b) ∨
  (b * b + c * c = a * a))
-- program terminates
∃ result, impl a b c = result ∧
-- return value satisfies spec
spec result

def implementation (a b c: Nat) : Bool := 
  0 < a && 0 < b && 0 < c &&
  ((a * a + b * b = c * c) ||
  (a * a + c * c = b * b) ||
  (b * b + c * c = a * a))

-- LLM HELPER
lemma Bool.and_eq_true_iff (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

-- LLM HELPER
lemma Bool.or_eq_true_iff (a b : Bool) : (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp

-- LLM HELPER
lemma decide_eq_true_iff (p : Prop) [Decidable p] : decide p = true ↔ p := by
  cases h : decide p <;> simp [h, decide_eq_true_iff_decide_eq_false]

theorem correctness
(a b c: Nat)
: problem_spec implementation a b c := by
  unfold problem_spec implementation
  simp only [exists_true_left]
  constructor
  · rfl
  · simp [Bool.and_eq_true_iff, Bool.or_eq_true_iff, decide_eq_true_iff]