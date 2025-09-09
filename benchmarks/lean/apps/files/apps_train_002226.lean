-- <vc-helpers>
-- </vc-helpers>

def count_valid_subsequences (n m : Nat) (a b : List Nat) : Nat := sorry

theorem count_valid_subsequences_nonnegative 
  (n m : Nat) (a b : List Nat) : 
  count_valid_subsequences n m a b ≥ 0 := sorry

theorem count_valid_subsequences_modulo_bound
  (n m : Nat) (a b : List Nat) :
  count_valid_subsequences n m a b < (10^9 + 7) := sorry

theorem increasing_arrays_valid
  (n m : Nat) (h1 : n > 0) (h2 : m > 0) (h3 : n ≤ 5) (h4 : m ≤ 5) :
  count_valid_subsequences n m (List.range' 1 n) (List.range' 1 m) ≥ 0 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_valid_subsequences 5 3 [1, 5, 2, 4, 7] [7, 9, 6]

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_valid_subsequences 4 2 [7, 7, 7, 7] [3, 4]

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible