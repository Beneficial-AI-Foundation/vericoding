-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_valid_subsequences (n m : Nat) (a b : List Nat) : Nat := sorry

theorem count_valid_subsequences_nonnegative 
  (n m : Nat) (a b : List Nat) : 
  count_valid_subsequences n m a b ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_valid_subsequences_modulo_bound
  (n m : Nat) (a b : List Nat) :
  count_valid_subsequences n m a b < (10^9 + 7) := sorry

theorem increasing_arrays_valid
  (n m : Nat) (h1 : n > 0) (h2 : m > 0) (h3 : n ≤ 5) (h4 : m ≤ 5) :
  count_valid_subsequences n m (List.range' 1 n) (List.range' 1 m) ≥ 0 := sorry
-- </vc-theorems>