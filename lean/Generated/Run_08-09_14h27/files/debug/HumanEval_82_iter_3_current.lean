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
    let rec check_divisors (n : Nat) (k: Nat) : Bool :=
      if k * k > n then true
      else if n % k = 0 then false
      else check_divisors n (k + 1)
    termination_by n - k
    decreasing_by
      simp_ww
      omega
    check_divisors n 2

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
lemma check_divisors_correct (n k : Nat) (h : 2 ≤ k) : 
  is_prime_bool.check_divisors n k = true ↔ (∀ x, k ≤ x → x < n → x * x ≤ n → ¬(n % x = 0)) := by
  sorry

-- LLM HELPER
lemma is_prime_bool_correct (n: Nat) : 
  is_prime_bool n = true ↔ (n ≥ 2 ∧ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0)) := by
  simp [is_prime_bool]
  constructor
  · intro h
    simp at h
    cases h_lt : n < 2 with
    | true =>
      simp [h_lt] at h
    | false =>
      simp [h_lt] at h
      constructor
      · omega
      · by_contra h_contra
        obtain ⟨k, hk_ge, hk_lt, hk_div⟩ := h_contra
        -- Use auxiliary lemma about check_divisors
        sorry
  · intro ⟨h_ge, h_no_div⟩
    simp
    have h_not_lt : ¬(n < 2) := by omega
    simp [h_not_lt]
    -- Use auxiliary lemma about check_divisors
    sorry

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · simp [implementation]
    rw [is_prime_bool_correct]

-- #test implementation "Hello" = True
-- #test implementation "abcdcba" = True
-- #test implementation "kittens" = True
-- #test implementation "orange" = False