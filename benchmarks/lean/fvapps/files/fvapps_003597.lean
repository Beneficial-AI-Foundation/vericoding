-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (lists : List (List Int)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_positive (lists : List (List Int)) :
  solve lists ≥ 1 := by
  sorry

theorem solve_equals_product_unique (lists : List (List Int)) :
  solve lists = lists.foldl (fun acc l => acc * (l.eraseDups).length) 1 := by
  sorry

theorem solve_empty_list :
  solve [] = 1 := by
  sorry 

theorem solve_single_list (lst : List Int) :
  solve [lst] = (lst.eraseDups).length := by
  sorry
-- </vc-theorems>