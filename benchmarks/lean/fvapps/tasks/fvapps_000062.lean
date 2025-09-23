-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Nat) (nums : List Nat) (friends : List Nat) : Nat := sorry 

theorem solve_case1 : 
  solve 4 2 [1, 13, 7, 17] [1, 3] = 48 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_case2 :
  solve 6 2 [10, 10, 10, 10, 11, 11] [3, 3] = 42 := sorry

theorem solve_case3 : 
  solve 4 4 [1000000000, 1000000000, 1000000000, 1000000000] [1, 1, 1, 1] = 8000000000 := sorry
-- </vc-theorems>