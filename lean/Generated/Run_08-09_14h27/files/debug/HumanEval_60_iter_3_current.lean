/- 
function_signature: "def sum_to_n(n: Nat) -> Nat"
docstring: |
    sum_to_n is a function that sums numbers from 1 to n.
test_cases:
  - input: 30
    expected_output: 465
  - input: 100
    expected_output: 4950
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (n: Nat) : Nat :=
  n * (n + 1) / 2

def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n : Nat) :=
-- spec
let spec (result: Nat) :=
  0 < n →
  (result = 1 ↔ n = 1) ∧
  (∀ i, implementation (i + 1) - (implementation i) = i + 1)
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
lemma implementation_recursive (i : Nat) : implementation (i + 1) - implementation i = i + 1 := by
  unfold implementation
  simp only [Nat.succ_mul]
  ring_nf
  omega

-- LLM HELPER  
lemma implementation_base : implementation 1 = 1 := by
  unfold implementation
  norm_num

-- LLM HELPER
lemma nat_mul_succ_even (n : Nat) : 2 ∣ (n * (n + 1)) := by
  cases Nat.mod_two_eq_zero_or_one n with
  | inl h_even => 
    rw [Nat.dvd_iff_mod_eq_zero] at h_even ⊢
    rw [Nat.mul_mod, h_even, zero_mul, zero_mod]
  | inr h_odd => 
    rw [Nat.dvd_iff_mod_eq_zero] at h_odd ⊢
    have h_succ_even : (n + 1) % 2 = 0 := by
      rw [Nat.add_mod, h_odd, Nat.one_mod]
      norm_num
    rw [Nat.mul_mod, h_succ_even, mul_zero, zero_mod]

-- LLM HELPER
lemma implementation_iff_one (n : Nat) (hn : 0 < n) : implementation n = 1 ↔ n = 1 := by
  constructor
  · intro h
    unfold implementation at h
    have h_pos : 0 < n * (n + 1) := Nat.mul_pos hn (Nat.succ_pos n)
    have h_div : n * (n + 1) / 2 * 2 = n * (n + 1) := Nat.div_mul_cancel (nat_mul_succ_even n)
    have h_eq : n * (n + 1) = 2 := by
      rw [← h_div, h, one_mul]
    by_cases h_cases : n = 1
    · exact h_cases
    · have h_ge : n ≥ 2 := Nat.succ_le_iff.mpr (Nat.lt_of_le_of_ne hn (Ne.symm h_cases))
      have : n * (n + 1) ≥ 2 * 3 := by
        apply Nat.mul_le_mul'
        · exact h_ge
        · exact Nat.succ_le_succ h_ge
      rw [h_eq] at this
      norm_num at this
  · intro h
    rw [h]
    exact implementation_base

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec
  simp
  use implementation n
  constructor
  · rfl
  · intro hn
    constructor
    · exact implementation_iff_one n hn
    · exact implementation_recursive

-- #test implementation 30 = 465
-- #test implementation 100 = 5050
-- #test implementation 5 = 15
-- #test implementation 10 = 55
-- #test implementation 1 = 1