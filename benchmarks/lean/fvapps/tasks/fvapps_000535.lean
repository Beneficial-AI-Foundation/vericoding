-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_cuts_for_skyscrapers (n : Nat) (heights : List Nat) : Nat := sorry

theorem cuts_non_negative (n : Nat) (heights : List Nat) :
  min_cuts_for_skyscrapers n heights ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_building_no_cuts (h : Nat) :
  min_cuts_for_skyscrapers 1 [h] = 0 := sorry

theorem cuts_non_negative_multi (n : Nat) (heights : List Nat) :
  n ≥ 2 → min_cuts_for_skyscrapers n heights ≥ 0 := sorry
-- </vc-theorems>