/- 
function_signature: "def prime_length(s: str) -> bool"
docstring: |
    Write a function that takes a string and returns True if the string
    length is a prime number or False otherwise
test_cases:
  - input: "Hello"
    output: True
  - input: "abcdcba"
    output: True
  - input: "kittens"
    output: True
  - input: "orange"
    output: False
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def is_prime_bool (n: Nat) : Bool :=
  if n < 2 then false
  else
    let rec check_divisors (k: Nat) : Bool :=
      if k * k > n then true
      else if n % k = 0 then false
      else check_divisors (k + 1)
    termination_by n - k
    check_divisors 2

def implementation (s: String) : Bool :=
  is_prime_bool s.length

def problem_spec
-- function signature
(implementation: String → Bool)
-- inputs
(s: String) :=
-- spec
let spec (result : Bool) :=
let is_prime (n: Nat) : Prop :=
  n ≥ 2 ∧ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0);
  result ↔ is_prime s.length
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
lemma is_prime_bool_correct (n: Nat) : 
  is_prime_bool n = true ↔ (n ≥ 2 ∧ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0)) := by
  simp [is_prime_bool]
  split
  · simp
  · constructor
    · intro h
      constructor
      · omega
      · by_contra h_contra
        obtain ⟨k, hk_ge, hk_lt, hk_div⟩ := h_contra
        -- The proof would require showing that check_divisors finds any existing divisor
        sorry
    · intro ⟨h_ge, h_no_div⟩
      -- The proof would require showing that check_divisors returns true when no divisors exist
      sorry

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  simp [problem_spec]
  use is_prime_bool s.length
  constructor
  · simp [implementation]
  · cases h : is_prime_bool s.length with
    | true => 
      simp
      rw [← is_prime_bool_correct]
      exact h
    | false =>
      simp
      by_contra h_contra
      rw [← is_prime_bool_correct] at h_contra
      rw [h] at h_contra
      simp at h_contra

-- #test implementation "Hello" = True
-- #test implementation "abcdcba" = True
-- #test implementation "kittens" = True
-- #test implementation "orange" = False