-- <vc-preamble>
def count_fibonacci_sequence (arr : List Int) : Nat :=
  let rec helper (i : Nat) (curr_max curr_fib : Nat) : Nat :=
    if i ≥ arr.length then curr_max
    else match arr.get? i, arr.get? (i-1), arr.get? (i-2) with
    | some x, some y, some z =>
      if x = y + z then
        helper (i+1) (max curr_max (curr_fib + 1)) (curr_fib + 1)
      else
        helper (i+1) curr_max 2
    | _, _, _ => curr_max
  termination_by arr.length - i
  helper 2 2 2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_sequence_length (n : Nat) (arr : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_max_sequence_length_empty :
  find_max_sequence_length 0 [] = 0 :=
sorry
-- </vc-theorems>