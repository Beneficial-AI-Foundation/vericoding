-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_jump (arr : List Nat) : Bool := sorry

theorem single_element_array_no_jump {arr : List Nat} (h : arr.length = 1) : 
  ¬(can_jump arr) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_first_element_no_jump {arr : List Nat} (h : arr.length ≥ 2) (h2 : arr.get? 0 = some 0) :
  ¬(can_jump arr) := sorry

theorem large_first_element_can_jump {arr : List Nat} (h : arr.length ≥ 2) 
  (h2 : arr.get? 0 = some (arr.length + 1)) :
  can_jump arr := sorry
-- </vc-theorems>