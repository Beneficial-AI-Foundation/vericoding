-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_changes (arr : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_bounds {arr : List Nat} : 
  0 ≤ find_min_changes arr ∧ find_min_changes arr ≤ arr.length :=
sorry

theorem identical_elements {n : Nat} {arr : List Nat} : 
  arr = List.replicate arr.length n → find_min_changes arr = 0 :=
sorry 

theorem increasing_sequence {arr : List Nat} :
  let sorted_unique := arr.eraseDups
  find_min_changes sorted_unique ≤ sorted_unique.length - 1 :=
sorry
-- </vc-theorems>