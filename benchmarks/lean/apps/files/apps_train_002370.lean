def number_of_steps (n: Nat) : Nat := sorry

def is_power_of_two (n: Nat) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def simulation_loop (n steps: Nat) : Nat :=
  match n with
  | 0 => steps
  | n+1 => if n % 2 = 0 
           then simulation_loop (n / 2) (steps + 1)
           else simulation_loop (n - 1) (steps + 1)

theorem number_of_steps_nonneg (n: Nat) : 
  number_of_steps n ≥ 0 := sorry

theorem zero_steps :
  number_of_steps 0 = 0 := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval number_of_steps 14

/-
info: 4
-/
-- #guard_msgs in
-- #eval number_of_steps 8

/-
info: 12
-/
-- #guard_msgs in
-- #eval number_of_steps 123

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible