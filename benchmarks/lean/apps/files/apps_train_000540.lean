def find_max_sequence_length (n : Nat) (arr : List Int) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

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

theorem find_max_sequence_length_empty :
  find_max_sequence_length 0 [] = 0 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_max_sequence_length 5 [2, 3, 5, 1, 2]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_max_sequence_length 3 [1, 2, 3]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_max_sequence_length 2 [1, 2]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible