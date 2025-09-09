-- <vc-helpers>
-- </vc-helpers>

def how_many_apples (n: Nat) : Nat :=
  sorry

theorem apples_always_positive {n: Nat} (h: n ≥ 2) :
  how_many_apples n > 0 :=
  sorry 

theorem apples_increases (n: Nat) (h: n ≥ 2) :  
  how_many_apples n > how_many_apples (n-1) :=
  sorry

theorem minimum_case :
  how_many_apples 2 = 7 :=
  sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval how_many_apples 2

/-
info: 3121
-/
-- #guard_msgs in
-- #eval how_many_apples 5

/-
info: 25
-/
-- #guard_msgs in
-- #eval how_many_apples 3

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible