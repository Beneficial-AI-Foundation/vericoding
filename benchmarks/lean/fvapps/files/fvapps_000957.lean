-- <vc-preamble>
def range_from_one (n : Nat) : List Nat :=
  List.range n |>.map (· + 1)

def list_to_string (l : List Nat) : String :=
  l.map toString |>.intersperse " " |>.foldl (· ++ ·) ""
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nums_to_nat_list (s : String) : List Nat := sorry

def find_building_arrangement (n k : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_distance_ascending (n : Nat) (h : n ≥ 2) :
  find_building_arrangement n 0 = list_to_string (range_from_one n) :=
sorry

theorem impossible_case_three_two :
  find_building_arrangement 3 2 = "CAPTAIN AMERICA EVADES" :=
sorry

theorem impossible_case_two_two :
  find_building_arrangement 2 2 = "CAPTAIN AMERICA EVADES" :=
sorry

theorem valid_arrangement_condition (n k : Nat) (s : String) :
  let nums := nums_to_nat_list s
  find_building_arrangement n k = s →
  (s = "CAPTAIN AMERICA EVADES" ∨
  (nums.length = n ∧
   nums.mergeSort (· ≤ ·) = range_from_one n ∧
   ∀ i j, i < nums.length → j < nums.length →
     (if i ≥ j then i - j else j - i) = k →
     (if nums[i]! ≥ nums[j]! then nums[i]! - nums[j]! else nums[j]! - nums[i]!) = 1))
  :=
sorry
-- </vc-theorems>