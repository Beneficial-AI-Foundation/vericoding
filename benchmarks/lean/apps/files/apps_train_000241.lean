-- <vc-helpers>
-- </vc-helpers>

def optimalDivision (nums: List Nat) : String := sorry

theorem optimal_division_empty (nums: List Nat) :
  nums = [] → optimalDivision nums = "" := sorry

theorem optimal_division_single (n: Nat) :
  optimalDivision [n] = toString n := sorry

theorem optimal_division_two (n m: Nat) :
  optimalDivision [n, m] = toString n ++ "/" ++ toString m := sorry

theorem division_format_parts (nums: List Nat) :
  nums.length ≥ 3 →
  let parts := (optimalDivision nums).splitOn "/"
  parts.length = nums.length ∧
  parts[0]! = toString nums[0]! ∧ 
  parts[1]!.startsWith "(" ∧
  parts[parts.length - 1]!.endsWith ")" := sorry

theorem first_number_preserved (nums: List Nat) :
  nums ≠ [] →
  (optimalDivision nums).startsWith (toString nums[0]!) := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible