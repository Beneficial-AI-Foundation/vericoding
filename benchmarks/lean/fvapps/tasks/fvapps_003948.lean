-- <vc-preamble>
def sum : List Int → Int
  | [] => 0
  | (h :: t) => h + sum t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_centered (arr : List Int) (n : Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_list_property (n : Int) :
  is_centered [] n = (n = 0) := sorry

theorem single_element_property {a : Int} :
  is_centered [a] (sum [a]) := sorry

theorem symmetric_property (arr : List Int) (n : Int) :
  is_centered arr n = is_centered arr.reverse n := sorry

theorem full_sum_property (arr : List Int) :
  arr ≠ [] → is_centered arr (sum arr) := sorry
-- </vc-theorems>