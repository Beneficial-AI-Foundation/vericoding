-- <vc-helpers>
-- </vc-helpers>

def next_day_of_week (current_day : Nat) (available_days : Nat) : Nat := sorry

def get_available_days (bit_pattern : Nat) : List Nat := sorry

theorem next_day_valid (current_day : Nat) (available_days : Nat)
  (h1 : 1 ≤ current_day) (h2 : current_day ≤ 7) (h3 : available_days ≤ 127) :
  let result := next_day_of_week current_day available_days
  1 ≤ result ∧ result ≤ 7 := sorry

theorem next_day_empty (current_day : Nat) (available_days : Nat)
  (h1 : 1 ≤ current_day) (h2 : current_day ≤ 7) (h3 : available_days = 0) :
  next_day_of_week current_day available_days = current_day := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval next_day_of_week 4 42

/-
info: 2
-/
-- #guard_msgs in
-- #eval next_day_of_week 6 42

/-
info: 2
-/
-- #guard_msgs in
-- #eval next_day_of_week 7 42

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible