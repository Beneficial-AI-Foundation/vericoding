-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shortest_sum_subsequence (n : Nat) (target : Int) (arr : List Int) : Int := sorry

def sum_list : List Int → Int 
  | [] => 0
  | x::xs => x + sum_list xs
-- </vc-definitions>

-- <vc-theorems>
theorem singleton_array (n : Int) :
  shortest_sum_subsequence 1 n [n] = 1 := sorry 

theorem edge_case_one : shortest_sum_subsequence 1 0 [1] = 1 := sorry

theorem edge_case_two : shortest_sum_subsequence 2 5 [2, 2] = -1 := sorry

theorem edge_case_three : shortest_sum_subsequence 3 3 [1, 1, 1] = 3 := sorry
-- </vc-theorems>