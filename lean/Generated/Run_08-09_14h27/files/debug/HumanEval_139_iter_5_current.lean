/- 
function_signature: "def special_factorial(n: int) -> int"
docstring: |
    The Brazilian factorial is defined as:
    brazilian_factorial(n) = n! * (n-1)! * (n-2)! * ... * 1!
    where n > 0. Please write a function that computes the Brazilian factorial.
test_cases:
  - input: 4
    expected_output: 288
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def brazilian_factorial : Nat → Nat
  | 0 => 1
  | n + 1 => Nat.factorial (n + 1) * brazilian_factorial n

def implementation (n: Nat) : Nat :=
  brazilian_factorial n

def problem_spec
-- function signature
(impl: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec_fn (result: Nat) :=
  let factorial := Nat.factorial n;
  (0 < n → result / factorial = impl (n - 1)) ∧
  (n = 0 → result = 1);
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec_fn result

-- LLM HELPER
lemma brazilian_factorial_zero : brazilian_factorial 0 = 1 := by
  rfl

-- LLM HELPER  
lemma brazilian_factorial_succ (n : Nat) : 
  brazilian_factorial (n + 1) = Nat.factorial (n + 1) * brazilian_factorial n := by
  rfl

-- LLM HELPER
lemma factorial_pos (n : Nat) : 0 < Nat.factorial n := by
  exact Nat.factorial_pos n

-- LLM HELPER
lemma brazilian_factorial_pos (n : Nat) : 0 < brazilian_factorial n := by
  induction n with
  | zero => 
    rw [brazilian_factorial_zero]
    norm_num
  | succ n ih =>
    rw [brazilian_factorial_succ]
    exact Nat.mul_pos (factorial_pos (n + 1)) ih

-- LLM HELPER
lemma div_mul_cancel_of_pos {a b : Nat} (h : 0 < a) : (a * b) / a = b := by
  exact Nat.mul_div_cancel_left b h

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec
  unfold implementation
  use brazilian_factorial n
  constructor
  · rfl
  · simp only []
    constructor
    · intro h
      cases n with
      | zero => 
        simp at h
      | succ k =>
        simp [Nat.factorial]
        rw [brazilian_factorial_succ]
        rw [div_mul_cancel_of_pos (factorial_pos (k + 1))]
        rfl
    · intro h
      rw [h]
      exact brazilian_factorial_zero

-- #test implementation 4 = 288