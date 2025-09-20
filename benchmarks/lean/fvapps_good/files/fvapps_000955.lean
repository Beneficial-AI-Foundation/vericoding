-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_even_odd_pairs (xs : List Nat) : Nat := sorry

theorem count_even_odd_pairs_empty :
  count_even_odd_pairs [] = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_even_odd_pairs_all_even :
  count_even_odd_pairs [2,4,6,1] = 3 := sorry

theorem count_even_odd_pairs_mixed1 :
  count_even_odd_pairs [1,2,1,3] = 2 := sorry

theorem count_even_odd_pairs_mixed2 :
  count_even_odd_pairs [5,4,1,2,3] = 3 := sorry

theorem count_even_odd_pairs_only_even :
  count_even_odd_pairs [2,4,6,8] = 0 := sorry

theorem count_even_odd_pairs_only_odd :
  count_even_odd_pairs [1,3,5,7] = 0 := sorry

theorem count_even_odd_pairs_alternating :
  count_even_odd_pairs [2,1,4,3,6,5] = 6 := sorry
-- </vc-theorems>