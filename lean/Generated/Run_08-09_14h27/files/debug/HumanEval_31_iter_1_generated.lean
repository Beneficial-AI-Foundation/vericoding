/- 
function_signature: "def is_prime(n)"
docstring: |
    Return true if a given number is prime, and false otherwise.
test_cases:
  - input: 6
    output: False
  - input: 101
    output: True
  - input: 11
    output: True
  - input: 13441
    output: True
  - input: 61
    output: True
  - input: 4
    output: False
  - input: 1
    output: False
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def has_divisor_in_range (n start limit : Nat) : Bool :=
  if start >= limit then false
  else if n % start = 0 then true
  else has_divisor_in_range n (start + 1) limit

def implementation (n: Nat): Bool :=
  if n < 2 then false
  else ¬(has_divisor_in_range n 2 n)

def problem_spec
-- function signature
(implementation: Nat → Bool)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Bool) :=
  result ↔ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0);
-- program termination
∃ result,
  implementation n = result ∧
  spec result

-- LLM HELPER
lemma has_divisor_in_range_correct (n start limit : Nat) :
  has_divisor_in_range n start limit = true ↔ ∃ k, start ≤ k ∧ k < limit ∧ n % k = 0 := by
  sorry

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec
  unfold implementation
  simp only [exists_prop]
  by_cases h : n < 2
  · -- Case: n < 2
    simp [h]
    constructor
    · -- Show false ↔ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0)
      constructor
      · intro h_false
        intro ⟨k, hk⟩
        have : k ≥ 2 := hk.1
        have : k < n := hk.2.1
        have : n < 2 := h
        linarith
      · intro h_no_div
        rfl
    · rfl
  · -- Case: n ≥ 2
    push_neg at h
    simp [h]
    simp only [Bool.not_eq_true]
    constructor
    · -- Show has_divisor_in_range n 2 n = false ↔ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0)
      constructor
      · intro h_no_div
        intro ⟨k, hk2, hkn, hdiv⟩
        sorry -- has_divisor_in_range returns false but k exists
      · intro h_no_exists
        by_contra h_contra
        sorry -- has_divisor_in_range returns true but no divisor exists
    · rfl

-- #test implementation 6 = false
-- #test implementation 101 = true
-- #test implementation 11 = true
-- #test implementation 13441 = true
-- #test implementation 61 = true
-- #test implementation 4 = false
-- #test implementation 1 = false