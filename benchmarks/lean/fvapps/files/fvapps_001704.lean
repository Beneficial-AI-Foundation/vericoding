-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_single_digit_addition (n : Nat) : Nat :=
sorry

def compute_running_sum : Nat → Nat
  | x => if x < 10 then x
         else compute_running_sum (solve_single_digit_addition x)
termination_by x => x
decreasing_by all_goals simp_wf; sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_single_digit (n : Nat) :
  solve_single_digit_addition n ≤ 9 :=
sorry

theorem result_equals_sum_of_digits (n : Nat) :
  let result := solve_single_digit_addition n
  let digit_sum := solve_single_digit_addition result
  result = digit_sum :=
sorry

theorem idempotent (n : Nat) :
  let first_result := solve_single_digit_addition n
  let second_result := solve_single_digit_addition first_result
  first_result = second_result :=
sorry

theorem equals_recursive_digit_sum (n : Nat) :
  solve_single_digit_addition n = compute_running_sum n :=
sorry
-- </vc-theorems>