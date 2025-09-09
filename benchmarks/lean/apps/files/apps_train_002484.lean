-- <vc-helpers>
-- </vc-helpers>

def split_numbers (s : String) : List String := sorry

theorem split_numbers_comma_separated (nums : List Nat) (h : nums.length > 0) : 
  split_numbers (String.intercalate "," (nums.map toString)) = 
  nums.map toString := sorry

theorem split_numbers_dot_separated (nums : List Nat) (h : nums.length > 0) : 
  split_numbers (String.intercalate "." (nums.map toString)) = 
  nums.map toString := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible