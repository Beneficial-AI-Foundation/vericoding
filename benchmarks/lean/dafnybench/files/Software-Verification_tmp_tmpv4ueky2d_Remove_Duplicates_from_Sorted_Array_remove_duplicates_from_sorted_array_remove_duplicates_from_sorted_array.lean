-- <vc-preamble>
def is_sorted (nums : Array Int) : Prop :=
∀ i j:Nat, 0 ≤ i → i < j → j < nums.size → nums[i]! ≤ nums[j]!
def is_sorted_and_distinct (nums : Array Int) : Prop :=
∀ i j:Nat, 0 ≤ i → i < j → j < nums.size → nums[i]! < nums[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remove_duplicates_from_sorted_array (nums : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem remove_duplicates_from_sorted_array_spec (nums : Array Int) :
is_sorted nums →
1 ≤ nums.size →
nums.size ≤ 30000 →
(∀ i, 0 ≤ i → i < nums.size → -100 ≤ nums[i]! ∧ nums[i]! ≤ 100) →
let result := remove_duplicates_from_sorted_array nums
is_sorted_and_distinct result ∧
(∀ x, (∃ i, 0 ≤ i ∧ i < nums.size ∧ nums[i]! = x) ↔
(∃ i, 0 ≤ i ∧ i < result.size ∧ result[i]! = x)) :=
sorry
-- </vc-theorems>