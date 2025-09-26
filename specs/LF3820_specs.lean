-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumNestedNumbers : NestedList Int → Int := sorry

def List.sum : List Int → Int 
  | [] => 0
  | x :: xs => x + List.sum xs
-- </vc-definitions>

-- <vc-theorems>
theorem flat_list_sum (lst : List Int) : 
  sumNestedNumbers (NestedList.list (lst.map NestedList.atom)) = lst.sum := sorry

theorem single_element (x : Int) : 
  sumNestedNumbers (NestedList.list [NestedList.atom x]) = x := sorry

theorem single_nested_element (x : Int) :
  sumNestedNumbers (NestedList.list [NestedList.list [NestedList.atom x]]) = x * x := sorry

theorem double_nested_element (x : Int) :
  sumNestedNumbers (NestedList.list [NestedList.list [NestedList.list [NestedList.atom x]]]) = 
    x * x * x := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval sum_nested_numbers [[0]]

/-
info: 15
-/
-- #guard_msgs in
-- #eval sum_nested_numbers [1, 2, 3, 4, 5]

/-
info: 149
-/
-- #guard_msgs in
-- #eval sum_nested_numbers [1, [2], 3, [4, [5]]]
-- </vc-theorems>