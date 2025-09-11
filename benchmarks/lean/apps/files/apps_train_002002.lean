-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def determine_location (n : Nat) (home_airport : String) (flights : List String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem determine_location_valid_output (n : Nat) (home_airport : String) (flights : List String) :
  determine_location n home_airport flights = "home" ∨ 
  determine_location n home_airport flights = "contest" :=
  sorry

theorem determine_location_parity (n : Nat) (home_airport : String) (flights : List String) :
  determine_location n home_airport flights = 
    if n % 2 = 1 then "contest" else "home" :=
  sorry

theorem determine_location_parity_simple (n : Nat) :
  determine_location n "ABC" [] = 
    if n % 2 = 1 then "contest" else "home" :=
  sorry

/-
info: 'home'
-/
-- #guard_msgs in
-- #eval determine_location 4 "SVO" ["SVO->CDG", "LHR->SVO", "SVO->LHR", "CDG->SVO"]

/-
info: 'contest'
-/
-- #guard_msgs in
-- #eval determine_location 3 "SVO" ["SVO->HKT", "HKT->SVO", "SVO->RAP"]

/-
info: 'contest'
-/
-- #guard_msgs in
-- #eval determine_location 1 "ESJ" ["ESJ->TSJ"]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded