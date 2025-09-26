-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.replicate (s : String) (n : Nat) : String :=
sorry

def count_safe_buildings (s : String) : Nat :=
sorry

def isSafeBuilding (s : String) (i : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_safe_buildings_equals_safe_spots (s : String) :
  count_safe_buildings s =
    (List.range s.length).foldl (fun acc i =>
      if isSafeBuilding s i then acc + 1 else acc) 0 :=
sorry

theorem count_safe_buildings_nonnegative (s : String) :
  count_safe_buildings s ≥ 0 :=
sorry

theorem count_safe_buildings_bounded (s : String) :
  count_safe_buildings s ≤ s.length :=
sorry

theorem all_zeros_returns_length (s : String) (n : Nat) :
  count_safe_buildings (String.replicate "0" n) = n :=
sorry

theorem all_ones_returns_zero (s : String) (n : Nat) :
  count_safe_buildings (String.replicate "1" n) = 0 :=
sorry

theorem empty_string_returns_zero :
  count_safe_buildings "" = 0 :=
sorry

theorem single_zero_returns_one :
  count_safe_buildings "0" = 1 :=
sorry

theorem single_one_returns_zero :
  count_safe_buildings "1" = 0 :=
sorry
-- </vc-theorems>