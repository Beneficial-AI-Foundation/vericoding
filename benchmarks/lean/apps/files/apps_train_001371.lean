-- <vc-preamble>
def String.replicate (s : String) (n : Nat) : String := sorry

-- Function signature we're reasoning about

def count_safe_buildings (s : String) : Nat := sorry

-- Properties from hypothesis test
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSafeBuilding (s : String) (i : Nat) : Bool := sorry 

theorem count_safe_buildings_equals_safe_spots (s : String) :
  count_safe_buildings s = 
    (List.range s.length).foldl (fun acc i => 
      if isSafeBuilding s i then acc + 1 else acc) 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_safe_buildings_nonnegative (s : String) :
  count_safe_buildings s ≥ 0 := sorry

theorem count_safe_buildings_bounded (s : String) :
  count_safe_buildings s ≤ s.length := sorry

-- Helper definition for checking if building at index i is safe

theorem all_zeros_returns_length (s : String) (n : Nat) :
  count_safe_buildings (String.replicate "0" n) = n := sorry

theorem all_ones_returns_zero (s : String) (n : Nat) :
  count_safe_buildings (String.replicate "1" n) = 0 := sorry

-- Edge cases

theorem empty_string_returns_zero :
  count_safe_buildings "" = 0 := sorry

theorem single_zero_returns_one :
  count_safe_buildings "0" = 1 := sorry

theorem single_one_returns_zero :
  count_safe_buildings "1" = 0 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_safe_buildings "010"

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_safe_buildings "10001"

/-
info: 7
-/
-- #guard_msgs in
-- #eval count_safe_buildings "0000000"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded