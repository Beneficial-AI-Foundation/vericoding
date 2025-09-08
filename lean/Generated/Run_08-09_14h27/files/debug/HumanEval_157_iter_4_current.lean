import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (a b c: Nat) : Bool :=
  0 < a && 0 < b && 0 < c && 
  (a * a + b * b = c * c || a * a + c * c = b * b || b * b + c * c = a * a)

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

-- LLM HELPER
lemma decide_and_equiv (p q : Prop) [Decidable p] [Decidable q] :
  (decide p = true ∧ decide q = true) ↔ (p ∧ q) := by
  constructor
  · intro h
    exact ⟨decide_eq_true.mp h.1, decide_eq_true.mp h.2⟩
  · intro h
    exact ⟨decide_eq_true.mpr h.1, decide_eq_true.mpr h.2⟩

-- LLM HELPER
lemma decide_or_equiv (p q r : Prop) [Decidable p] [Decidable q] [Decidable r] :
  (decide p = true ∨ decide q = true ∨ decide r = true) ↔ (p ∨ q ∨ r) := by
  constructor
  · intro h
    cases h with
    | inl h1 => exact Or.inl (decide_eq_true.mp h1)
    | inr h2 => 
      cases h2 with
      | inl h3 => exact Or.inr (Or.inl (decide_eq_true.mp h3))
      | inr h4 => exact Or.inr (Or.inr (decide_eq_true.mp h4))
  · intro h
    cases h with
    | inl h1 => exact Or.inl (decide_eq_true.mpr h1)
    | inr h2 =>
      cases h2 with
      | inl h3 => exact Or.inr (Or.inl (decide_eq_true.mpr h3))
      | inr h4 => exact Or.inr (Or.inr (decide_eq_true.mpr h4))

theorem correctness
(a b c: Nat)
: problem_spec implementation a b c := by
  unfold problem_spec implementation
  use (0 < a && 0 < b && 0 < c && 
       (a * a + b * b = c * c || a * a + c * c = b * b || b * b + c * c = a * a))
  constructor
  · rfl
  · simp only [Bool.and_eq_true, Bool.or_eq_true]
    constructor
    · intro h
      have h1 : (0 < a ∧ 0 < b) ∧ 0 < c := by
        have := decide_and_equiv (0 < a ∧ 0 < b) (0 < c)
        rw [← this]
        have h_and : decide (0 < a) = true ∧ decide (0 < b) = true := by
          have := decide_and_equiv (0 < a) (0 < b)
          rw [← this]
          exact h.1.1
        exact ⟨h_and, h.1.2⟩
      have h2 : (a * a + b * b = c * c ∨ a * a + c * c = b * b ∨ b * b + c * c = a * a) := by
        have := decide_or_equiv (a * a + b * b = c * c) (a * a + c * c = b * b) (b * b + c * c = a * a)
        rw [← this]
        exact h.2
      exact ⟨h1.1.1, h1.1.2, h1.2, h2⟩
    · intro h
      constructor
      constructor
      · have := decide_and_equiv (0 < a) (0 < b)
        rw [this]
        exact ⟨h.1, h.2.1⟩
      · rw [decide_eq_true]
        exact h.2.2.1
      · have := decide_or_equiv (a * a + b * b = c * c) (a * a + c * c = b * b) (b * b + c * c = a * a)
        rw [this]
        exact h.2.2.2

-- #test implementation ([1, 2, 2, -4]: List Int) = (-9: Int)
-- #test implementation ([0, 1]: List Int) = (0: Int)
-- #test implementation ([]: List Int) = none