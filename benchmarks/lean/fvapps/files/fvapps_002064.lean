-- <vc-preamble>
def List.maximum (l: List Nat) : Nat :=
match l with
| [] => 0
| (x::xs) => List.foldl Nat.max x xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_max_generating_set (numbers: List Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem one_in_gen_set (numbers: List Nat) (h: numbers ≠ []) : 
  1 ∈ min_max_generating_set numbers :=
sorry

theorem max_output_bounded (numbers: List Nat) (h: numbers ≠ []) :
  ∀ x ∈ min_max_generating_set numbers, x ≤ List.maximum numbers :=
sorry

theorem output_size_bounded (numbers: List Nat) :
  List.length (min_max_generating_set numbers) ≤ List.length numbers :=
sorry
-- </vc-theorems>