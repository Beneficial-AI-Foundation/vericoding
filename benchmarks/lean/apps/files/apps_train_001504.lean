-- <vc-preamble>
def MOD := 1000000007

def calculate_possible_schedules (n : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pow (base n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_possible_schedules_mod_bounds (n : Nat) :
  0 ≤ calculate_possible_schedules n ∧ calculate_possible_schedules n < MOD :=
  sorry

theorem calculate_possible_schedules_odd_even_match (n : Nat) :
  calculate_possible_schedules n = 
    if n % 2 = 0 
    then ((pow 3 n) + 3) % MOD
    else ((pow 3 n) - 3) % MOD :=
  sorry

/-
info: 12
-/
-- #guard_msgs in
-- #eval calculate_possible_schedules 2

/-
info: 24
-/
-- #guard_msgs in
-- #eval calculate_possible_schedules 3

/-
info: 240
-/
-- #guard_msgs in
-- #eval calculate_possible_schedules 5
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded