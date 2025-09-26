-- <vc-preamble>
def find_single_element (arr : List Int) : Int :=
  sorry

def is_valid_input (arr : List Int) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_duplicate (x : Int) : List Int := [x, x]

theorem find_single_element_sorted {nums : List Int} 
  (h₁ : nums.length ≥ 2)
  (h₂ : ∀ i, i + 1 < nums.length → nums[i]! ≤ nums[i+1]!)
  (h₃ : ∀ x ∈ nums, x ≥ -1000 ∧ x ≤ 1000) :
  let doubles := (nums.take (nums.length - 1)).map list_duplicate |>.join
  let last := nums[nums.length - 1]!
  let result := doubles ++ [last]
  find_single_element result = last := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_single_element_position {nums : List Int} 
  (h₁ : nums.length > 0)
  (h₂ : nums.length ≤ 9)
  (h₃ : ∀ i, i + 1 < nums.length → nums[i]! ≤ nums[i+1]!)
  (h₄ : ∀ x ∈ nums, x ≥ -1000 ∧ x ≤ 1000)
  (i : Nat)
  (h₅ : i < nums.length) :
  let before := (nums.take i).map list_duplicate |>.join
  let single := [nums[i]'h₅]
  let after := (nums.drop (i+1)).map list_duplicate |>.join
  let result := before ++ single ++ after
  is_valid_input result →
  find_single_element result = nums[i]'h₅ :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_single_element [1, 1, 2, 3, 3, 4, 4, 8, 8]

/-
info: 10
-/
-- #guard_msgs in
-- #eval find_single_element [3, 3, 7, 7, 10, 11, 11]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_single_element [1, 1, 2, 2, 3]
-- </vc-theorems>