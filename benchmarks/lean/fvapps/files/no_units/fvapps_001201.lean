-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_infection_severity (passengers : List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem severity_matches_manual_calc
    (coords : List (Int × Int)) :
    let passengers := coords.map (fun (x : Int × Int) => s!"{x.1} {x.2}")
    let manual_calc := coords.foldl (fun acc x => (acc + (x.2 - x.1).natAbs + 1) % (10^9 + 7)) 0
    calculate_infection_severity passengers = manual_calc :=
sorry

theorem zero_distance_severity
    (xs : List Int) :
    let passengers := xs.map (fun x => s!"{x} {x}")
    calculate_infection_severity passengers = xs.length :=
sorry
-- </vc-theorems>