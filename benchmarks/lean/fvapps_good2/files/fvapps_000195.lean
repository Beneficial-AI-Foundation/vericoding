-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest_consecutive (nums : List Int) : Nat :=
sorry

def removeDuplicates (nums : List Int) : List Int :=
sorry

def sortList (nums : List Int) : List Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_nonnegative (nums : List Int) :
  longest_consecutive nums ≥ 0 :=
sorry

theorem same_as_deduplicated (nums : List Int) :
  longest_consecutive nums = longest_consecutive (removeDuplicates nums) :=
sorry

theorem sorted_same_as_unsorted (nums : List Int) :
  nums ≠ [] → longest_consecutive nums = longest_consecutive (sortList nums) :=
sorry

theorem output_leq_input_len (nums : List Int) :
  longest_consecutive nums ≤ nums.length :=
sorry

theorem empty_list_zero (nums : List Int) :
  nums = [] → longest_consecutive nums = 0 :=
sorry

theorem single_element_one (nums : List Int) (x : Int) :
  nums = [x] → longest_consecutive nums = 1 :=
sorry

theorem reversed_same (nums : List Int) :
  nums ≠ [] → longest_consecutive nums = longest_consecutive nums.reverse :=
sorry
-- </vc-theorems>