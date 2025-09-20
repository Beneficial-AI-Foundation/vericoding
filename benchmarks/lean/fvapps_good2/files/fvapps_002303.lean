-- <vc-preamble>
def isSorted (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def searchInsert (nums : List Int) (target : Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem searchInsert_valid_index
    {nums : List Int} {target : Int}
    (h1 : List.length nums > 0)
    (h2 : isSorted nums) :
    let result := searchInsert nums target
    0 ≤ result ∧ result ≤ nums.length :=
sorry

theorem searchInsert_left_smaller
    {nums : List Int} {target : Int}
    (h1 : List.length nums > 0)
    (h2 : isSorted nums) :
    let result := searchInsert nums target
    ∀ i, i < result → nums[i]! < target :=
sorry

theorem searchInsert_right_greater_eq
    {nums : List Int} {target : Int}
    (h1 : List.length nums > 0)
    (h2 : isSorted nums) :
    let result := searchInsert nums target
    ∀ i, result ≤ i → i < nums.length → nums[i]! ≥ target :=
sorry

theorem searchInsert_maintains_order
    {nums : List Int} {target : Int}
    (h1 : List.length nums > 0)
    (h2 : isSorted nums) :
    let result := searchInsert nums target
    let inserted := (nums.take result).append (target :: nums.drop result)
    isSorted inserted :=
sorry

theorem searchInsert_identity
    {nums : List Int}
    (h1 : List.length nums > 0)
    (h2 : isSorted nums)
    {i : Nat} (h3 : i < nums.length) :
    searchInsert nums nums[i]! = List.findIdx (· = nums[i]!) nums :=
sorry
-- </vc-theorems>