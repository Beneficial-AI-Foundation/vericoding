import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Nat → Nat × Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat × Nat) :=
  let is_palindrome (k: Nat): Prop :=
    List.Palindrome (Nat.digits 10 k);
  let even_palindrome (k: Nat): Prop :=
    (Even k) ∧ (is_palindrome k);
  let odd_palindrome (k: Nat): Prop :=
    (Odd k) ∧ (is_palindrome k);
  n > 0 →
  (1 < n →
    let impl_n_minus_1 := implementation (n - 1);
    ((even_palindrome n) → result.1 = 1 + impl_n_minus_1.1) ∧
    ((odd_palindrome n) → result.2 = 1 + impl_n_minus_1.2) ∧
    (¬ (odd_palindrome n) → result.2 = impl_n_minus_1.2) ∧
    (¬ (even_palindrome n) → result.1 = impl_n_minus_1.1))
  ∧
  (n = 1 → (result.1 = 0) ∧ (result.2 = 1));
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def is_palindrome (k: Nat): Prop :=
  List.Palindrome (Nat.digits 10 k)

-- LLM HELPER
def even_palindrome (k: Nat): Prop :=
  (Even k) ∧ (is_palindrome k)

-- LLM HELPER
def odd_palindrome (k: Nat): Prop :=
  (Odd k) ∧ (is_palindrome k)

-- LLM HELPER
instance (n: Nat) : Decidable (is_palindrome n) := by
  unfold is_palindrome
  exact List.decidablePalindrome

-- LLM HELPER
instance (n: Nat) : Decidable (even_palindrome n) := by
  unfold even_palindrome
  exact instDecidableAnd

-- LLM HELPER
instance (n: Nat) : Decidable (odd_palindrome n) := by
  unfold odd_palindrome
  exact instDecidableAnd

def implementation (n: Nat) : Nat × Nat := 
  if n = 0 then (0, 0)
  else if n = 1 then (0, 1)
  else
    let prev := implementation (n - 1)
    let even_count := if even_palindrome n then prev.1 + 1 else prev.1
    let odd_count := if odd_palindrome n then prev.2 + 1 else prev.2
    (even_count, odd_count)

-- LLM HELPER
lemma one_is_odd_palindrome : odd_palindrome 1 := by
  constructor
  · exact Nat.odd_iff.mpr rfl
  · simp [is_palindrome]
    rw [Nat.digits]
    simp [Nat.digitsAux]
    constructor
    · simp
    · simp

-- LLM HELPER
lemma implementation_eq_helper (n: Nat) (h: n ≠ 0) (h': n ≠ 1) : 
  implementation n = 
  let prev := implementation (n - 1)
  let even_count := if even_palindrome n then prev.1 + 1 else prev.1
  let odd_count := if odd_palindrome n then prev.2 + 1 else prev.2
  (even_count, odd_count) := by
  simp [implementation]
  split_ifs with h1 h2
  · contradiction
  · contradiction
  · rfl

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · intro h_pos
    constructor
    · intro h_gt_one
      have h_ne_zero : n ≠ 0 := Nat.ne_of_gt h_pos
      have h_ne_one : n ≠ 1 := Nat.ne_of_gt h_gt_one
      rw [implementation_eq_helper n h_ne_zero h_ne_one]
      simp only [even_palindrome, odd_palindrome]
      constructor
      · intro h_even_pal
        simp [h_even_pal]
      · constructor
        · intro h_odd_pal
          simp [h_odd_pal]
        · constructor
          · intro h_not_odd_pal
            simp [h_not_odd_pal]
          · intro h_not_even_pal
            simp [h_not_even_pal]
    · intro h_eq_one
      simp [implementation, h_eq_one]