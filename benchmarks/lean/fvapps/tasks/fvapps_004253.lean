-- <vc-preamble>
def is_sorted_increasing (xs : List Nat) : Prop :=
  ∀ i j, i < j → j < xs.length → xs[i]! ≤ xs[j]!

def is_sorted_decreasing (xs : List Nat) : Prop :=
  ∀ i j, i < j → j < xs.length → xs[i]! ≥ xs[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def order_type {α : Type} (arr : List α) : String := sorry

def lengthOf (α : Type) : α → Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem constant_length_elements {α : Type} [Inhabited α] (arr : List α) :
  arr.length > 0 →
  (∀ i j, i < arr.length → j < arr.length → lengthOf α (arr[i]!) = lengthOf α (arr[j]!)) →
  order_type arr = "Constant" :=
sorry

theorem increasing_length_numbers (arr : List Nat) :
  arr.length > 0 →
  is_sorted_increasing (arr.map (λ x => lengthOf Nat x)) →
  (∃ i j, i < arr.length → j < arr.length → lengthOf Nat (arr[i]!) ≠ lengthOf Nat (arr[j]!)) →
  order_type arr = "Increasing" :=
sorry

theorem decreasing_length_lists (arr : List (List Nat)) :
  arr.length > 0 →
  is_sorted_decreasing (arr.map List.length) →
  (∃ i j, i < arr.length → j < arr.length → (arr[i]!).length ≠ (arr[j]!).length) →
  order_type arr = "Decreasing" :=
sorry

theorem unsorted_mixed_types {α : Type} [Inhabited α] (arr : List α) :
  arr.length > 0 →
  ¬ is_sorted_increasing (arr.map (lengthOf α)) →
  ¬ is_sorted_decreasing (arr.map (lengthOf α)) →
  (∃ i j, i < arr.length → j < arr.length → lengthOf α (arr[i]!) ≠ lengthOf α (arr[j]!)) →
  order_type arr = "Unsorted" :=
sorry

theorem empty_list {α : Type} :
  order_type ([] : List α) = "Constant" :=
sorry
-- </vc-theorems>