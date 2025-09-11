-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumOddLengthSubarrays (arr : List Int) : Int := sorry

def manualSum (arr : List Int) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_element_arr_eq_result (x : Int) : 
  sumOddLengthSubarrays [x] = x := sorry

theorem result_eq_manual_sum (arr : List Int) :
  sumOddLengthSubarrays arr = manualSum arr := sorry

theorem positive_input_positive_output (arr : List Int) :
  (∀ x ∈ arr, x > 0) → sumOddLengthSubarrays arr > 0 := sorry

/-
info: 58
-/
-- #guard_msgs in
-- #eval sum_odd_length_subarrays [1, 4, 2, 5, 3]

/-
info: 3
-/
-- #guard_msgs in
-- #eval sum_odd_length_subarrays [1, 2]

/-
info: 66
-/
-- #guard_msgs in
-- #eval sum_odd_length_subarrays [10, 11, 12]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded