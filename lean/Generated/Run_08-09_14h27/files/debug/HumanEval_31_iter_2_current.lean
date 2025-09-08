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
  induction' limit using Nat.strong_induction with limit ih
  simp [has_divisor_in_range]
  by_cases h1 : start >= limit
  · simp [h1]
    constructor
    · intro h
      exact False.elim h
    · intro ⟨k, hstart, hlimit, hdiv⟩
      exact Nat.not_le.mpr hstart h1
  · simp [h1]
    by_cases h2 : n % start = 0
    · simp [h2]
      constructor
      · intro
        exact ⟨start, le_refl start, Nat.not_le.mp h1, h2⟩
      · intro
        rfl
    · simp [h2]
      have h_lt : start + 1 ≤ limit := by
        push_neg at h1
        exact Nat.succ_le_of_lt h1
      rw [ih (start + 1) h_lt]
      constructor
      · intro ⟨k, hstart_succ, hlimit, hdiv⟩
        exact ⟨k, Nat.le_trans (Nat.le_succ start) hstart_succ, hlimit, hdiv⟩
      · intro ⟨k, hstart, hlimit, hdiv⟩
        by_cases h3 : k = start
        · subst h3
          exact False.elim (h2 hdiv)
        · exact ⟨k, Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hstart h3), hlimit, hdiv⟩

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec
  unfold implementation
  simp only [exists_and_left]
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
        rw [← has_divisor_in_range_correct] at h_no_div
        have : has_divisor_in_range n 2 n = true := by
          rw [has_divisor_in_range_correct]
          exact ⟨k, hk2, hkn, hdiv⟩
        rw [this] at h_no_div
        exact h_no_div
      · intro h_no_exists
        by_contra h_contra
        rw [has_divisor_in_range_correct] at h_contra
        obtain ⟨k, hk2, hkn, hdiv⟩ := h_contra
        exact h_no_exists ⟨k, hk2, hkn, hdiv⟩
    · rfl