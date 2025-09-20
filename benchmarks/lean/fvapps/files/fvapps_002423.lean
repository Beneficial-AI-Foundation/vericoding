-- <vc-preamble>
def isSorted (nums: List Int) : Bool :=
  match nums with
  | [] => true
  | [_] => true
  | x::y::rest => x ≤ y && isSorted (y::rest)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_monotonic (nums: List Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_or_single_element_lists_monotonic (nums: List Int) :
  nums.length ≤ 1 → is_monotonic nums :=
sorry

theorem identical_elements_monotonic (nums: List Int) (x: Int) (h: nums.length ≥ 2) :
  (∀ i: Fin nums.length, nums.get i = x) → is_monotonic nums :=
sorry

theorem sorted_lists_monotonic (nums: List Int) (h: nums.length ≥ 2) :
  isSorted nums → is_monotonic nums :=
sorry

theorem non_monotonic_lists_false (nums: List Int) (h: nums.length ≥ 3) :
  (∀ i: Fin nums.length, ∀ j: Fin nums.length,
    i.val + 1 = j.val → ¬(nums.get i ≤ nums.get j)) ∧
  (∀ i: Fin nums.length, ∀ j: Fin nums.length,
    i.val + 1 = j.val → ¬(nums.get i ≥ nums.get j)) →
  ¬is_monotonic nums :=
sorry
-- </vc-theorems>