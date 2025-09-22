-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_good_permutation (n : Nat) (arr : List Nat) : Bool := sorry

theorem single_element_permutation_valid (n : Nat) :
  n = 1 → is_good_permutation n [1] = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem basic_properties_sorted (n : Nat) (arr : List Nat) :
  arr = List.range' 1 n → is_good_permutation n arr = true := sorry

theorem small_permutations_valid (n : Nat) (arr : List Nat) :
  n ≤ 2 → arr = List.range' 1 n → is_good_permutation n arr = true := sorry 

theorem decreasing_sequence_invalid (n : Nat) :
  n ≥ 3 → 
  let arr := List.reverse (List.range' 1 n)
  is_good_permutation n arr = false := sorry
-- </vc-theorems>