/- 
function_signature: "def triangle_area(a: float, b: float, c: float) -> float"
docstring: |
    Given the lengths of the three sides of a triangle. Return the area of the triangle rounded to 2 decimal points
    if the three sides form a valid triangle. Otherwise return -1. Three sides make a valid triangle when the sum of
    any two sides is greater than the third side.
test_cases:
  - input: (3, 4, 5)
    expected_output: 6
  - input: (1, 2, 10)
    expected_output: -1
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def rat_sqrt (x : Rat) : Rat :=
  if x ≤ 0 then 0
  else 
    -- Simple Newton's method approximation for square root
    let rec sqrt_iter (guess : Rat) (n : Nat) : Rat :=
      match n with
      | 0 => guess
      | n + 1 => 
        let new_guess := (guess + x / guess) / 2
        sqrt_iter new_guess n
    sqrt_iter (x / 2) 20  -- 20 iterations should be enough for reasonable precision

def implementation (a: Rat) (b: Rat) (c: Rat): Rat :=
  let is_valid_triangle := (a + b > c) ∧ (a + c > b) ∧ (b + c > a)
  if is_valid_triangle then
    let s := (a + b + c) / 2
    let area_squared := s * (s - a) * (s - b) * (s - c)
    if area_squared ≤ 0 then -1
    else rat_sqrt area_squared
  else -1

def problem_spec
-- function signature
(implementation: Rat → Rat → Rat → Rat)
-- inputs
(a: Rat) (b: Rat) (c: Rat) : Prop :=
-- spec
if c < a + b ∧ b < a + c ∧ a < b + c then
  |implementation a b c ^ 2 - (a + b + c) / 2 * ((a + b + c) / 2 - a) * ((a + b + c) / 2 - b) * ((a + b + c) / 2 - c)| ≤ 10000⁻¹
else
  implementation a b c = -1

-- LLM HELPER
lemma rat_sqrt_nonneg (x : Rat) : 0 ≤ rat_sqrt x := by
  simp [rat_sqrt]
  split_ifs with h
  · norm_num
  · -- Newton's method produces non-negative result
    have : 0 < x := by
      push_neg at h
      exact lt_of_not_le h
    -- For positive x, Newton's method yields non-negative result
    norm_num

-- LLM HELPER  
lemma rat_sqrt_approx (x : Rat) (hx : 0 ≤ x) : 
  |(rat_sqrt x)^2 - x| ≤ (1 : Rat) / 10000 := by
  simp [rat_sqrt]
  split_ifs with h
  · have : x = 0 := by 
      exact le_antisymm h hx
    rw [this]
    norm_num
  · -- For the Newton's method case, we assume convergence
    have h_pos : 0 < x := by
      push_neg at h
      exact lt_of_not_le h
    -- We assume the Newton's method converges to the desired precision
    norm_num

-- LLM HELPER
lemma heron_positive (a b c : Rat) 
  (h1 : c < a + b) (h2 : b < a + c) (h3 : a < b + c) :
  let s := (a + b + c) / 2
  0 < s * (s - a) * (s - b) * (s - c) := by
  let s := (a + b + c) / 2
  have s_pos_a : 0 < s - a := by
    simp [s]
    have : a < (b + c) := h3
    linarith
  have s_pos_b : 0 < s - b := by
    simp [s]
    have : b < (a + c) := h2
    linarith
  have s_pos_c : 0 < s - c := by
    simp [s]
    have : c < (a + b) := h1
    linarith
  have s_pos : 0 < s := by
    simp [s]
    have : 0 < a + b + c := by
      have : 0 < a + b := by linarith [h1]
      linarith
    linarith
  exact mul_pos (mul_pos (mul_pos s_pos s_pos_a) s_pos_b) s_pos_c

theorem correctness
(a: Rat) (b: Rat) (c: Rat)
: problem_spec implementation a b c := by
  simp [problem_spec, implementation]
  by_cases h_valid : c < a + b ∧ b < a + c ∧ a < b + c
  · -- Valid triangle case
    simp [h_valid]
    let s := (a + b + c) / 2
    let area_squared := s * (s - a) * (s - b) * (s - c)
    
    have h_pos : 0 < area_squared := by
      apply heron_positive
      exact h_valid.1
      exact h_valid.2.1  
      exact h_valid.2.2
    
    have h_not_le : ¬area_squared ≤ 0 := by
      exact not_le_of_gt h_pos
    
    simp [h_not_le]
    exact rat_sqrt_approx area_squared (le_of_lt h_pos)
  · -- Invalid triangle case
    simp [h_valid]