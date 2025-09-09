-- <vc-helpers>
-- </vc-helpers>

def find_peak_element (nums : List Int) : Int := sorry 

theorem find_peak_element_valid_index {nums : List Int} (h : nums ≠ []) : 
  let idx := find_peak_element nums
  0 ≤ idx ∧ idx < nums.length := sorry

theorem single_element_peak {nums : List Int} (h : nums.length = 1) :
  find_peak_element nums = 0 := sorry

theorem peak_at_start {nums : List Int} {idx : Nat} 
  (h₁ : find_peak_element nums = 0) 
  (h₂ : nums ≠ []) :
  nums.get! 0 ≥ nums.get! 1 ∨ nums.length = 1 := sorry

theorem peak_at_end {nums : List Int} {idx : Nat}
  (h₁ : find_peak_element nums = nums.length - 1)
  (h₂ : nums ≠ []) :
  nums.get! (nums.length - 1) ≥ nums.get! (nums.length - 2) := sorry

theorem peak_in_middle {nums : List Int} {idx : Nat}
  (h₁ : find_peak_element nums = idx)
  (h₂ : 0 < idx)
  (h₃ : idx < nums.length - 1) :
  nums.get! idx ≥ nums.get! (idx - 1) ∨ 
  nums.get! idx ≥ nums.get! (idx + 1) := sorry

theorem empty_array :
  find_peak_element [] = -1 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_peak_element [1, 2, 3, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_peak_element [1]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible