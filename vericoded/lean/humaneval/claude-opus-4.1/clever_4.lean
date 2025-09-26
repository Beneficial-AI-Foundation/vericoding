-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def implementation (numbers: List Rat) : Rat :=
  if numbers.length = 0 then 0 else
  (numbers.map (fun x => abs (x * numbers.length - numbers.sum))).sum / (numbers.length * numbers.length)
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: List Rat → Rat)
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: Rat):=
0 < numbers.length →
0 ≤ result ∧
result * numbers.length * numbers.length =
(numbers.map (fun x => |x * numbers.length - numbers.sum|)).sum;
-- program terminates
∃ result, implementation numbers = result ∧
-- return value satisfies spec
spec result

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  by_cases h : numbers.length = 0
  · use 0
    constructor
    · simp [implementation, h]
    · intro h_pos
      simp [h] at h_pos
  · use ((numbers.map (fun x => abs (x * numbers.length - numbers.sum))).sum / (numbers.length * numbers.length))
    constructor
    · simp [implementation, h]
    · intro h_pos
      constructor
      · apply div_nonneg
        · apply List.sum_nonneg
          intro x hx
          simp at hx
          obtain ⟨y, _, rfl⟩ := hx
          exact abs_nonneg _
        · have pos_len : (0 : ℚ) < numbers.length := by
            rw [Nat.cast_pos]
            exact h_pos
          exact le_of_lt (mul_self_pos.mpr (ne_of_gt pos_len))
      · field_simp
        ring
-- </vc-theorems>

-- #test implementation [1.0, 2.0, 3.0, 4.0] = 1.0