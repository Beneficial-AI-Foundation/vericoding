-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def split_numbers (s : String) : List String := sorry

theorem split_numbers_comma_separated (nums : List Nat) (h : nums.length > 0) : 
  split_numbers (String.intercalate "," (nums.map toString)) = 
  nums.map toString := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem split_numbers_dot_separated (nums : List Nat) (h : nums.length > 0) : 
  split_numbers (String.intercalate "." (nums.map toString)) = 
  nums.map toString := sorry
-- </vc-theorems>