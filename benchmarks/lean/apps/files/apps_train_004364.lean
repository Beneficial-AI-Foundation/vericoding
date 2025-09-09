-- <vc-helpers>
-- </vc-helpers>

def finance (n : Int) : Int := sorry

theorem finance_non_negative (n : Nat) :
  finance n ≥ 0 ∧ 
  finance n = n * (n + 1) * (n + 2) / 2 := sorry

theorem finance_strictly_increasing {n : Nat} (h : n > 0) :
  finance n > finance (n - 1) := sorry

/-
info: 105
-/
-- #guard_msgs in
-- #eval finance 5

/-
info: 168
-/
-- #guard_msgs in
-- #eval finance 6

/-
info: 360
-/
-- #guard_msgs in
-- #eval finance 8

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible