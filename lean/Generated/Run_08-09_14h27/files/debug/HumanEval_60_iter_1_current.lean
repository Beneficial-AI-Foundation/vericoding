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
lemma sum_formula (n : Nat) : n * (n + 1) / 2 = (List.range (n + 1)).sum := by
  induction n with
  | zero => simp [List.range, List.sum]
  | succ k ih =>
    rw [List.range_succ_eq_map, List.sum_cons, List.sum_range_add_one]
    simp [Nat.succ_mul, Nat.add_div_two_of_odd]
    omega

-- LLM HELPER
lemma implementation_recursive (i : Nat) : implementation (i + 1) - implementation i = i + 1 := by
  unfold implementation
  simp only [Nat.succ_mul, Nat.add_mul]
  ring_nf
  omega

-- LLM HELPER  
lemma implementation_base : implementation 1 = 1 := by
  unfold implementation
  norm_num

-- LLM HELPER
lemma implementation_iff_one (n : Nat) (hn : 0 < n) : implementation n = 1 ↔ n = 1 := by
  constructor
  · intro h
    unfold implementation at h
    have : n * (n + 1) = 2 := by
      rw [← Nat.mul_div_cancel_left 2 (by norm_num : 0 < 2)] at h
      rw [← h]
      exact Nat.mul_div_cancel_left (n * (n + 1)) (by norm_num)
    have : n * n + n = 2 := by simp [Nat.mul_succ] at this; exact this
    omega
  · intro h
    rw [h]
    exact implementation_base

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
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