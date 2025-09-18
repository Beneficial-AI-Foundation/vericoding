-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_longest_segment (n : Nat) (k : Nat) (nums : List Nat) : Nat := sorry 

-- Basic properties from known good test cases
-- </vc-definitions>

-- <vc-theorems>
theorem solve_basic_case_1 :
  solve_longest_segment 5 3 [2, 4, 2, 4, 2] = 5 := sorry

theorem solve_basic_case_2 : 
  solve_longest_segment 8 5 [9, 3, 5, 7, 8, 11, 17, 2] = 3 := sorry

theorem solve_repeated_number :
  solve_longest_segment 4 3 [2, 4, 4, 2] = 4 := sorry
-- </vc-theorems>