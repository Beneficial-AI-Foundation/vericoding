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
  (a * a + b * b == c * c || 
   a * a + c * c == b * b || 
   b * b + c * c == a * a)

-- LLM HELPER
lemma bool_and_eq_true_iff (p q : Bool) : (p && q) = true ↔ p = true ∧ q = true := by
  cases p <;> cases q <;> simp

-- LLM HELPER
lemma bool_or_eq_true_iff (p q r : Bool) : (p || q || r) = true ↔ p = true ∨ q = true ∨ r = true := by
  cases p <;> cases q <;> cases r <;> simp

-- LLM HELPER
lemma nat_lt_decidable_eq_true_iff (n : Nat) : (0 < n) ↔ (decide (0 < n)) = true := by
  simp [decide_eq_true_iff]

-- LLM HELPER
lemma nat_eq_decidable_eq_true_iff (n m : Nat) : (n = m) ↔ (decide (n = m)) = true := by
  simp [decide_eq_true_iff]

theorem correctness
(a b c: Nat)
: problem_spec implementation a b c := by
  unfold problem_spec implementation
  simp only [exists_prop]
  constructor
  · rfl
  · simp only [Bool.coe_true_iff, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    constructor
    · intro h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      exact h
    · intro h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
      exact h