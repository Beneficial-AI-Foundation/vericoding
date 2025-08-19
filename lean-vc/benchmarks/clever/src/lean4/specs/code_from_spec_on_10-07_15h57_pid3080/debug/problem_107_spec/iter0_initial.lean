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
def is_palindrome_num (k: Nat): Bool :=
  let digits := Nat.digits 10 k
  digits == digits.reverse

-- LLM HELPER
def count_palindromes_helper (n: Nat) : Nat × Nat :=
  if n = 0 then (0, 0)
  else if n = 1 then (0, 1)
  else
    let prev := count_palindromes_helper (n - 1)
    let even_count := if Even n && is_palindrome_num n then prev.1 + 1 else prev.1
    let odd_count := if Odd n && is_palindrome_num n then prev.2 + 1 else prev.2
    (even_count, odd_count)

def implementation (n: Nat) : Nat × Nat := count_palindromes_helper n

-- LLM HELPER
lemma digits_palindrome_equiv (k: Nat) : 
  is_palindrome_num k = true ↔ List.Palindrome (Nat.digits 10 k) := by
  simp [is_palindrome_num, List.Palindrome]
  rw [List.eq_reverse_iff_palindrome]

-- LLM HELPER
lemma base_case_n_eq_1 : count_palindromes_helper 1 = (0, 1) := by
  simp [count_palindromes_helper]

-- LLM HELPER
lemma recursive_case (n: Nat) (h: 1 < n) : 
  count_palindromes_helper n = 
  let prev := count_palindromes_helper (n - 1)
  let even_count := if Even n && is_palindrome_num n then prev.1 + 1 else prev.1
  let odd_count := if Odd n && is_palindrome_num n then prev.2 + 1 else prev.2
  (even_count, odd_count) := by
  simp [count_palindromes_helper]
  have : n ≠ 0 := by omega
  have : n ≠ 1 := by omega
  simp [this]

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec, implementation]
  use count_palindromes_helper n
  constructor
  · rfl
  · intro h_pos
    constructor
    · intro h_gt_1
      simp [recursive_case n h_gt_1]
      let is_palindrome := fun k => List.Palindrome (Nat.digits 10 k)
      let even_palindrome := fun k => Even k ∧ is_palindrome k
      let odd_palindrome := fun k => Odd k ∧ is_palindrome k
      constructor
      · intro h_even_pal
        simp [even_palindrome] at h_even_pal
        have : Even n ∧ is_palindrome_num n = true := by
          constructor
          · exact h_even_pal.1
          · rw [digits_palindrome_equiv]
            exact h_even_pal.2
        simp [this]
      constructor
      · intro h_odd_pal
        simp [odd_palindrome] at h_odd_pal
        have : Odd n ∧ is_palindrome_num n = true := by
          constructor
          · exact h_odd_pal.1
          · rw [digits_palindrome_equiv]
            exact h_odd_pal.2
        simp [this]
      constructor
      · intro h_not_odd_pal
        have : ¬(Odd n ∧ is_palindrome_num n = true) := by
          intro h
          apply h_not_odd_pal
          constructor
          · exact h.1
          · rw [← digits_palindrome_equiv]
            exact h.2
        simp [this]
      · intro h_not_even_pal
        have : ¬(Even n ∧ is_palindrome_num n = true) := by
          intro h
          apply h_not_even_pal
          constructor
          · exact h.1
          · rw [← digits_palindrome_equiv]
            exact h.2
        simp [this]
    · intro h_eq_1
      rw [h_eq_1]
      exact base_case_n_eq_1