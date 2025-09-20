-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_binary_additions (s1 s2 : String) : Nat := sorry

theorem zeros_add_no_carry : 
  count_binary_additions "0" "0" = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem one_zero_no_carry :
  count_binary_additions "1" "0" = 0 := sorry 

theorem zero_one_one_carry :
  count_binary_additions "0" "1" = 1 := sorry
-- </vc-theorems>