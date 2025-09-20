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
-- </vc-theorems>