-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def most_frequent_item_count (lst : List Int) : Nat := sorry

theorem most_frequent_item_count_nonneg (lst : List Int) :
  most_frequent_item_count lst ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem most_frequent_item_count_bounded (lst : List Int) :
  most_frequent_item_count lst ≤ lst.length := sorry

theorem most_frequent_item_count_upper_bound (lst : List Int) (x : Int) :
  x ∈ lst → (lst.count x) ≤ most_frequent_item_count lst := sorry

theorem most_frequent_item_count_exists (lst : List Int) :
  most_frequent_item_count lst > 0 →
  ∃ x ∈ lst, lst.count x = most_frequent_item_count lst := sorry

theorem most_frequent_item_count_nonempty (lst : List Int) :
  lst ≠ [] → most_frequent_item_count lst ≥ 1 := sorry

theorem most_frequent_item_count_empty :
  most_frequent_item_count [] = 0 := sorry
-- </vc-theorems>