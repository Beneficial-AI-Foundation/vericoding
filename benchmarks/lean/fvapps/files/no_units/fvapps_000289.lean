-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min (nums: List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_singleton :
  find_min [1] = 1 :=
  sorry

theorem find_min_all_equal :
  find_min [1, 1, 1] = 1 :=
  sorry

theorem find_min_rotated_with_zero :
  find_min [2, 2, 2, 0, 2] = 0 :=
  sorry
-- </vc-theorems>