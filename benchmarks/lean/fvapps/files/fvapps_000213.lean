-- <vc-preamble>
def countUnique (l: List Nat) : Nat :=
  (List.foldl (fun acc x => if acc.contains x then acc else x::acc) [] l).length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def subarrayBitwiseORs (nums: List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_nonnegative {nums: List Nat} (h: nums ≠ []) :
  subarrayBitwiseORs nums ≥ 0 :=
sorry

theorem result_upper_bound {nums: List Nat} (h: nums ≠ []) :
  subarrayBitwiseORs nums ≤ (nums.length * (nums.length + 1)) / 2 :=
sorry

theorem single_element_subarray {nums: List Nat} (h: nums ≠ []) :
  subarrayBitwiseORs nums ≥ countUnique nums :=
sorry
-- </vc-theorems>