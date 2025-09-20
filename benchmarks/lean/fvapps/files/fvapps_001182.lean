-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_digits_function (n : Nat) : Nat := sorry

def solve_sequence_sum (first diff left right : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_digits_function_bounds (x : Nat) (h : x ≥ 1) :
  let result := sum_digits_function x
  1 ≤ result ∧ result ≤ 9 ∧ result = sum_digits_function result := sorry

theorem sequence_sum_zero_diff (first length left : Nat) (h : length > 0) :
  let right := left + length - 1
  solve_sequence_sum first 0 left right = length * sum_digits_function first := sorry

theorem sequence_sum_bounds (first diff left length : Nat) 
  (h1 : first > 0) (h2 : diff > 0) (h3 : left > 0) (h4 : length > 0) :
  let right := left + length - 1
  let result := solve_sequence_sum first diff left right
  length ≤ result ∧ result ≤ 9 * length := sorry

theorem sequence_sum_single_element (first diff pos : Nat)
  (h1 : first > 0) (h2 : diff > 0) (h3 : pos > 0) :
  solve_sequence_sum first diff pos pos = 
    sum_digits_function (first + diff * (pos - 1)) := sorry

theorem sequence_sum_order_invariant (first diff left delta : Nat)
  (h1 : first > 0) :
  let right := left + delta
  left = right → 
    solve_sequence_sum first diff left right = 
    solve_sequence_sum first diff right left := sorry
-- </vc-theorems>