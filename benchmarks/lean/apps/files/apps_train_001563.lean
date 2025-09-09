-- <vc-helpers>
-- </vc-helpers>

def count_change (money : Int) (coins : List Int) : Int :=
  sorry

theorem count_change_no_coins (money : Int) :
  count_change money [] = (if money = 0 then 1 else 0) :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_change 4 [1, 2]

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_change 10 [5, 2, 3]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_change 11 [5, 7]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible