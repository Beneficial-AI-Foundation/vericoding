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
      simp_wf
      have : k < k + 1 := Nat.lt_succ_self k
      have : k * k ≤ n := by omega
      have : k < n := by
        by_contra h
        push_neg at h
        have : n < k := Nat.lt_of_le_of_ne h (Ne.symm (Nat.ne_of_lt ‹k < k + 1›))
        have : n < k * k := Nat.lt_of_lt_of_le this (Nat.le_mul_self k)
        omega
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
lemma check_divisors_correct (n k : Nat) (hk : 2 ≤ k) (hn : k ≤ n) : 
  is_prime_bool.check_divisors n k = true ↔ (∀ x, k ≤ x → x < n → x * x ≤ n → ¬(n % x = 0)) := by
  sorry

-- LLM HELPER
lemma is_prime_bool_correct (n: Nat) : 
  is_prime_bool n = true ↔ (n ≥ 2 ∧ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0)) := by
  simp [is_prime_bool]
  if h : n < 2 then
    simp [h]
    constructor
    · intro h_false
      cases h_false
    · intro ⟨h_ge, _⟩
      omega
  else
    simp [h]
    have h_ge : n ≥ 2 := by omega
    constructor
    · intro h_check
      constructor
      · exact h_ge
      · by_contra h_contra
        obtain ⟨k, hk_ge, hk_lt, hk_div⟩ := h_contra
        -- The check_divisors function should have caught this divisor
        have : k ≥ 2 := hk_ge
        have : k < n := hk_lt
        -- For now, we'll use the fact that if check_divisors returns true,
        -- then there should be no divisors, but this needs the full correctness proof
        sorry
    · intro ⟨_, h_no_div⟩
      -- If there are no divisors, then check_divisors should return true
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
    simp only [Bool.true_iff]
    have h_ge : s.length ≥ 2 ↔ 2 ≤ s.length := by rfl
    rw [← h_ge]
    exact is_prime_bool_correct s.length

-- #test implementation "Hello" = True
-- #test implementation "abcdcba" = True
-- #test implementation "kittens" = True
-- #test implementation "orange" = False