-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_jewels (jewels stones : String) : Nat :=
  sorry

def reverseString (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_jewels_properties_non_negative (jewels stones : String) :
  count_jewels jewels stones ≥ 0 :=
sorry

theorem count_jewels_bounded_by_stones (jewels stones : String) :
  count_jewels jewels stones ≤ stones.length :=
sorry

theorem count_jewels_empty_jewels (stones : String) :
  count_jewels "" stones = 0 :=
sorry

theorem count_jewels_empty_stones (jewels : String) :
  count_jewels jewels "" = 0 :=
sorry

theorem count_jewels_duplicates (jewels stones : String) :
  count_jewels (jewels ++ jewels) stones = count_jewels jewels stones :=
sorry
-- </vc-theorems>