-- <vc-helpers>
-- </vc-helpers>

def friends (n : Nat) : Nat := sorry

theorem zero_or_one_jar_no_friends (n : Nat) (h : n ≤ 1) : friends n = 0 := sorry

theorem sufficient_friends (n : Nat) (h : n ≥ 2) : 
  2^(friends n + 1) ≥ n := sorry

theorem friends_monotone (n : Nat) (h : n ≥ 2) :
  friends n ≥ friends (n-1) := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval friends 0

/-
info: 0
-/
-- #guard_msgs in
-- #eval friends 1

/-
info: 1
-/
-- #guard_msgs in
-- #eval friends 4

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible