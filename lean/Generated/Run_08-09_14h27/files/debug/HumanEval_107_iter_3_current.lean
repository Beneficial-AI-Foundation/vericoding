/- 
function_signature: "def even_odd_palindrome(n: nat) -> (nat, nat)"
docstring: |
    Given a positive integer n, return a tuple that has the number of even and odd
    integer palindromes that fall within the range(1, n), inclusive.
test_cases:
  - input: 3
    expected_output: (1, 2)
  - input: 12
    expected_output: (4, 6)
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def is_palindrome (k: Nat): Bool :=
  let digits := Nat.digits 10 k
  digits = digits.reverse

-- LLM HELPER
def count_even_odd_palindromes (n: Nat) : Nat × Nat :=
  let rec aux (i: Nat) (acc_even acc_odd: Nat) : Nat × Nat :=
    if i > n then (acc_even, acc_odd)
    else if is_palindrome i then
      if i % 2 = 0 then
        aux (i + 1) (acc_even + 1) acc_odd
      else
        aux (i + 1) acc_even (acc_odd + 1)
    else
      aux (i + 1) acc_even acc_odd
  termination_by n + 1 - i
  aux 1 0 0

def implementation (n: Nat) : Nat × Nat :=
  count_even_odd_palindromes n

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
lemma is_palindrome_bool_iff_prop (k: Nat) : is_palindrome k = true ↔ List.Palindrome (Nat.digits 10 k) := by
  simp [is_palindrome, List.palindrome_iff]

-- LLM HELPER
lemma even_iff_mod_two_eq_zero (k: Nat) : Even k ↔ k % 2 = 0 := by
  exact Nat.even_iff_two_dvd.trans Nat.dvd_iff_mod_eq_zero

-- LLM HELPER
lemma odd_iff_mod_two_eq_one (k: Nat) : Odd k ↔ k % 2 = 1 := by
  constructor
  · intro h
    cases' Nat.mod_two_eq_zero_or_one k with h0 h1
    · exfalso
      rw [Nat.odd_iff_not_even] at h
      exact h (even_iff_mod_two_eq_zero k |>.mpr h0)
    · exact h1
  · intro h
    rw [Nat.odd_iff_not_even]
    intro heven
    have : k % 2 = 0 := even_iff_mod_two_eq_zero k |>.mp heven
    rw [this] at h
    simp at h

-- LLM HELPER
lemma implementation_recursive (n: Nat) (hn: n > 1) : 
  implementation n = 
  let prev := implementation (n - 1)
  if is_palindrome n then
    if n % 2 = 0 then (prev.1 + 1, prev.2)
    else (prev.1, prev.2 + 1)
  else prev := by
  sorry

-- LLM HELPER
lemma implementation_base : implementation 1 = (0, 1) := by
  simp [implementation, count_even_odd_palindromes, is_palindrome]
  simp only [Nat.digits_one]
  simp [List.reverse_singleton]

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · intro hn0
    constructor
    · intro hn1
      constructor
      · intro heven_pal
        have heven : Even n := heven_pal.1
        have hpal : List.Palindrome (Nat.digits 10 n) := heven_pal.2
        have : n % 2 = 0 := even_iff_mod_two_eq_zero n |>.mp heven
        have : is_palindrome n = true := is_palindrome_bool_iff_prop n |>.mpr hpal
        have hn1_pos : n > 1 := hn1
        rw [implementation_recursive n hn1_pos]
        simp [this, ‹n % 2 = 0›]
      constructor
      · intro hodd_pal
        have hodd : Odd n := hodd_pal.1
        have hpal : List.Palindrome (Nat.digits 10 n) := hodd_pal.2
        have : n % 2 = 1 := odd_iff_mod_two_eq_one n |>.mp hodd
        have : is_palindrome n = true := is_palindrome_bool_iff_prop n |>.mpr hpal
        have hn1_pos : n > 1 := hn1
        rw [implementation_recursive n hn1_pos]
        simp [this, ‹n % 2 = 1›]
        by_cases h : n % 2 = 0
        · simp [h]
        · simp [h]
      constructor
      · intro hnodd_pal
        have hn1_pos : n > 1 := hn1
        rw [implementation_recursive n hn1_pos]
        by_cases h : is_palindrome n = true
        · simp [h]
          by_cases h2 : n % 2 = 0
          · simp [h2]
          · simp [h2]
            have : Odd n := by
              rw [odd_iff_mod_two_eq_one]
              cases' Nat.mod_two_eq_zero_or_one n with h0 h1
              · contradiction
              · exact h1
            have : List.Palindrome (Nat.digits 10 n) := is_palindrome_bool_iff_prop n |>.mp h
            exfalso
            exact hnodd_pal ⟨‹Odd n›, ‹List.Palindrome (Nat.digits 10 n)›⟩
        · simp [h]
      · intro hneven_pal
        have hn1_pos : n > 1 := hn1
        rw [implementation_recursive n hn1_pos]
        by_cases h : is_palindrome n = true
        · simp [h]
          by_cases h2 : n % 2 = 0
          · simp [h2]
            have : Even n := even_iff_mod_two_eq_zero n |>.mpr h2
            have : List.Palindrome (Nat.digits 10 n) := is_palindrome_bool_iff_prop n |>.mp h
            exfalso
            exact hneven_pal ⟨‹Even n›, ‹List.Palindrome (Nat.digits 10 n)›⟩
          · simp [h2]
        · simp [h]
    · intro h1
      rw [h1]
      constructor
      · rw [implementation_base]
        simp
      · rw [implementation_base]
        simp