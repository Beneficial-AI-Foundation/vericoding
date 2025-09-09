-- <vc-helpers>
-- </vc-helpers>

def f (n : Nat) : Nat := sorry
def m (n : Nat) : Nat := sorry

theorem f_non_negative (n : Nat) : f n ≥ 0 := sorry

theorem m_non_negative (n : Nat) : m n ≥ 0 := sorry

theorem f_less_than_input (n : Nat) : n > 0 → f n ≤ n := sorry

theorem m_less_than_input (n : Nat) : n > 0 → m n ≤ n := sorry

theorem f_base_case : f 0 = 1 := sorry

theorem m_base_case : m 0 = 0 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval f 0

/-
info: 3
-/
-- #guard_msgs in
-- #eval f 5

/-
info: 6
-/
-- #guard_msgs in
-- #eval f 10

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible