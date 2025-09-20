-- <vc-preamble>
def isMultipleOf3 (x : Nat) : Bool := x % 3 == 0

def isMultipleOf5 (x : Nat) : Bool := x % 5 == 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solution (n : Nat) : Array Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solution_output_format (n : Nat) (h : n > 0) :
  (solution n).size = 3 ∧
  ∀ i < 3, (solution n)[i]! ≥ 0 :=
sorry

theorem solution_sum_matches_multiples (n : Nat) (h : n > 0) :
  let result := solution n
  let total := result[0]! + result[1]! + result[2]!
  let multiples := (List.range n).filter (fun x => isMultipleOf3 x || isMultipleOf5 x)
  total = multiples.length :=
sorry

theorem solution_component_counts (n : Nat) (h : n > 0) :
  let result := solution n
  let only3 := (List.range n).filter (fun x => isMultipleOf3 x && !isMultipleOf5 x)
  let only5 := (List.range n).filter (fun x => isMultipleOf5 x && !isMultipleOf3 x)
  let both := (List.range n).filter (fun x => isMultipleOf3 x && isMultipleOf5 x)
  result[0]! = only3.length ∧
  result[1]! = only5.length ∧
  result[2]! = both.length :=
sorry

theorem solution_edge_cases :
  solution 1 = #[0, 0, 0] ∧
  solution 3 = #[0, 0, 0] ∧
  solution 4 = #[1, 0, 0] :=
sorry
-- </vc-theorems>