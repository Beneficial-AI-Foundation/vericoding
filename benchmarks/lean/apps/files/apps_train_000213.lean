-- <vc-preamble>
def subarrayBitwiseORs (nums: List Nat) : Nat := sorry

theorem result_is_nonnegative {nums: List Nat} (h: nums ≠ []) :
  subarrayBitwiseORs nums ≥ 0 := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countUnique (l: List Nat) : Nat := 
  (List.foldl (fun acc x => if acc.contains x then acc else x::acc) [] l).length
-- </vc-definitions>

-- <vc-theorems>
theorem result_upper_bound {nums: List Nat} (h: nums ≠ []) :
  subarrayBitwiseORs nums ≤ (nums.length * (nums.length + 1)) / 2 := sorry

theorem single_element_subarray {nums: List Nat} (h: nums ≠ []) :
  subarrayBitwiseORs nums ≥ countUnique nums := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval subarrayBitwiseORs [0]

/-
info: 3
-/
-- #guard_msgs in
-- #eval subarrayBitwiseORs [1, 1, 2]

/-
info: 6
-/
-- #guard_msgs in
-- #eval subarrayBitwiseORs [1, 2, 4]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded