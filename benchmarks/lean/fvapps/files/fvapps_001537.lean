-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_base_plans (n : Nat) (grid : List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem diagonal_case (n : Nat) :
  let diagonal := List.range n |>.map (fun i =>
    String.mk (List.range n |>.map (fun j => if i = j then '1' else '0')))
  solve_base_plans n diagonal = n * (n + 1) / 2 :=
  sorry

theorem empty_grid_one :
  solve_base_plans 1 ["1"] = 1 :=
  sorry

theorem empty_grid_zero :
  solve_base_plans 1 ["0"] = 0 :=
  sorry

theorem all_zeros (n : Nat) :
  let zeros := List.replicate n (String.mk (List.replicate n '0'))
  solve_base_plans n zeros = 0 :=
  sorry
-- </vc-theorems>