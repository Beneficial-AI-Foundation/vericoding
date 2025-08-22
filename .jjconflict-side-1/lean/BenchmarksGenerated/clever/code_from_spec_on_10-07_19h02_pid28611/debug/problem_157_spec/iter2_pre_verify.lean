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

-- LLM HELPER
lemma implementation_correct_iff (a b c : Nat) : 
  implementation a b c = true ↔ 
  0 < a ∧ 0 < b ∧ 0 < c ∧ 
  (a * a + b * b = c * c ∨ a * a + c * c = b * b ∨ b * b + c * c = a * a) := by
  unfold implementation
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    cases h with
    | mk h1 h2 =>
      cases h1 with
      | mk h3 h4 =>
        cases h3 with
        | mk h5 h6 =>
          exact ⟨h5, h6, h4, h2⟩
  · intro h
    cases h with
    | mk h1 h2 =>
      cases h2 with
      | mk h3 h4 =>
        cases h4 with
        | mk h5 h6 =>
          exact ⟨⟨⟨h1, h3⟩, h5⟩, h6⟩

theorem correctness
(a b c: Nat)
: problem_spec implementation a b c := by
  unfold problem_spec
  simp only [exists_prop]
  use implementation a b c
  constructor
  · rfl
  · exact implementation_correct_iff a b c