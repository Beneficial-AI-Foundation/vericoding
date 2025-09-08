/- 
function_signature: "def fizz_buzz(n: int)"
docstring: |
    Return the number of times the digit 7 appears in integers less than n which are divisible by 11 or 13.
test_cases:
  - input: 50
    output: 0
  - input: 78
    output: 2
  - input: 79
    output: 3
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def count_sevens_in_nat (n : Nat) : Nat :=
  n.repr.count '7'

-- LLM HELPER
def is_divisible_by_11_or_13 (n : Nat) : Bool :=
  n % 11 = 0 || n % 13 = 0

def implementation (n: Nat) : Nat :=
  (List.range n).filter (fun i => (i % 11 = 0 || i % 13 = 0)) |>.map count_sevens_in_nat |>.sum

def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
  (n = 0 → result = 0) ∧
  (0 < n → result = implementation (n - 1) →
    (n % 11 ≠  0 ∧  n % 13 ≠  0) ∨ n.repr.count '7' = 0) ∧
  (0 < n → result ≠ implementation (n - 1) →
    (n % 11 = 0 ∨  n % 13 = 0) ∧
    result - implementation (n - 1) = n.repr.count '7')
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
lemma implementation_zero : implementation 0 = 0 := by
  simp [implementation]

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  constructor
  · intro h
    rw [h]
    exact implementation_zero
  constructor
  · intro h_pos result_eq
    left
    simp
    tauto
  · intro h_pos result_neq
    constructor
    · by_contra h_not_div
      push_neg at h_not_div
      simp at h_not_div
      have : implementation n = implementation (n - 1) := by
        simp [implementation]
        have : List.range n = List.range (n - 1) ++ [n - 1] := by
          rw [← Nat.sub_add_cancel (Nat.succ_le_of_lt h_pos)]
          simp [List.range_succ]
        rw [this]
        simp [List.filter_append, List.map_append, List.sum_append]
        simp [List.filter_cons]
        simp [h_not_div]
      exact result_neq this
    · omega