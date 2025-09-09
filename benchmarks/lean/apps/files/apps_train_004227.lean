def WEEKDAY : Nat → String := sorry
def ERROR : String := sorry

-- <vc-helpers>
-- </vc-helpers>

def whatday (n : Int) : String := sorry

theorem whatday_spec (n : Int) :
  (1 ≤ n ∧ n ≤ 7 → ∃ (i : Nat), whatday n = WEEKDAY i) ∧
  (¬(1 ≤ n ∧ n ≤ 7) → whatday n = ERROR) := sorry

theorem valid_weekday (n : Int) (h : 1 ≤ n ∧ n ≤ 7) :
  ∃ (i : Nat), whatday n = WEEKDAY i := sorry

theorem invalid_weekday (n : Int) (h : ¬(1 ≤ n ∧ n ≤ 7)) :
  whatday n = ERROR := sorry

/-
info: 'Sunday'
-/
-- #guard_msgs in
-- #eval whatday 1

/-
info: 'Saturday'
-/
-- #guard_msgs in
-- #eval whatday 7

/-
info: ERROR
-/
-- #guard_msgs in
-- #eval whatday 0

-- Apps difficulty: introductory
-- Assurance level: unguarded