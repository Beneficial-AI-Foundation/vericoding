-- <vc-preamble>
def stringContainsArrow (s : String) : Bool :=
  s.any (· = '-') && s.any (· = '>')

def stringToRange (s : String) : Option (Int × Int) :=
  if !stringContainsArrow s then none
  else
    let parts := s.splitOn "->"
    match parts with
    | [start, stop] => some (start.toInt!, stop.toInt!)
    | _ => none
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def summary_ranges (nums : List Int) : List String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem summary_ranges_empty (nums : List Int) :
  nums = [] → summary_ranges nums = [] :=
sorry

theorem summary_ranges_singleton (n : Int) :
  summary_ranges [n] = [toString n] :=
sorry

theorem summary_ranges_valid_ranges (nums : List Int) (range_str : String) :
  range_str ∈ summary_ranges nums →
  match stringContainsArrow range_str with
  | true =>
      let range := stringToRange range_str
      match range with
      | some (start, stop) =>
          start ≤ stop ∧
          ∀ x, start ≤ x ∧ x ≤ stop → x ∈ nums
      | none => True
  | false => range_str.toInt! ∈ nums :=
sorry

theorem summary_ranges_consecutive (nums : List Int) :
  nums ≠ [] →
  nums.length ≥ 2 →
  (∀ i, i + 1 < nums.length → nums[i+1]! = nums[i]! + 1) →
  summary_ranges nums = [s!"{nums.get! 0}->{nums.get! (nums.length - 1)}"] :=
sorry
-- </vc-theorems>