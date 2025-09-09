-- <vc-helpers>
-- </vc-helpers>

def custom_fib (signature : List Int) (indexes : List Int) (n : Nat) : Int :=
  sorry

theorem known_sequence_1 :
  custom_fib [1,1] [0,1] 3 = 3 :=
sorry

theorem known_sequence_2 :
  custom_fib [0,1] [0,1] 5 = 5 :=
sorry

theorem known_sequence_3 :
  custom_fib [1,2,3] [0,1,2] 3 = 6 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval custom_fib [1, 1] [0, 1] 2

/-
info: 17
-/
-- #guard_msgs in
-- #eval custom_fib [3, 5, 2] [0, 1, 2] 4

/-
info: 2
-/
-- #guard_msgs in
-- #eval custom_fib [7, 3, 4, 1] [1, 1] 6

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible