-- <vc-helpers>
-- </vc-helpers>

def count_bad_prices (prices : List Int) : Nat := sorry

theorem count_bad_prices_non_negative (prices : List Int) :
  count_bad_prices prices ≥ 0 := sorry

theorem count_bad_prices_upper_bound (prices : List Int) : 
  count_bad_prices prices ≤ prices.length := sorry

theorem count_bad_prices_singleton (price : Int) :
  count_bad_prices [price] = 0 := sorry

theorem count_bad_prices_empty :
  count_bad_prices [] = 0 := sorry

theorem count_bad_prices_all_same (n : Nat) (x : Int) :
  count_bad_prices (List.replicate n x) = 0 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_bad_prices [3, 9, 4, 6, 7, 5]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_bad_prices [1000000]

/-
info: 8
-/
-- #guard_msgs in
-- #eval count_bad_prices [31, 41, 59, 26, 53, 58, 97, 93, 23, 84]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible