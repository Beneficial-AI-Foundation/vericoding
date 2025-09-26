-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_boxes (k : Nat) (n : List Nat) (boxes : List (List Nat)) : (Bool × Option (List Nat) × Option (List Nat)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_boxes_single_box :
  solve_boxes 1 [1] [[42]] = (true, some [42], some [0])
  := sorry 

theorem solve_boxes_multibox :
  solve_boxes 4 [3,2,2,1] [[1,7,4], [3,2], [8,5], [10]] = 
    (true, some [7,2,5,10], some [1,2,0,3])
  := sorry

theorem solve_boxes_impossible_diff_values :
  solve_boxes 2 [1,1] [[1],[2]] = (false, none, none)
  := sorry

theorem solve_boxes_impossible_same_values :
  solve_boxes 2 [1,1] [[1],[1]] = (false, none, none)
  := sorry
-- </vc-theorems>