-- <vc-helpers>
-- </vc-helpers>

def count_divisible_by_k (n k : Nat) (nums : List Int) : Nat :=
  sorry

theorem empty_list_count (n k : Nat) (h1 : n > 0) (h2 : k > 0) :
    count_divisible_by_k n k [] = 0 :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_divisible_by_k 7 3 [1, 51, 966369, 7, 9, 999996, 11]

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_divisible_by_k 4 2 [2, 3, 4, 8]

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_divisible_by_k 3 5 [5, 10, 12]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible