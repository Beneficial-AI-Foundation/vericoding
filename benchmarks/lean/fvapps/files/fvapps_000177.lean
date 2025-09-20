-- <vc-preamble>
def list_sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => x + list_sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_refuel_stops (target : Nat) (start_fuel : Nat) (stations : List (Nat × Nat)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_refuel_stops_result_valid (target : Nat) (start_fuel : Nat)
    (stations : List (Nat × Nat)) :
  let result := min_refuel_stops target start_fuel stations
  result ≥ -1 :=
sorry

theorem min_refuel_stops_sufficient_start_fuel (target : Nat) (start_fuel : Nat)
    (stations : List (Nat × Nat)) :
  start_fuel ≥ target →
  min_refuel_stops target start_fuel stations = 0 :=
sorry

theorem min_refuel_stops_impossible (target : Nat) (start_fuel : Nat)
    (stations : List (Nat × Nat)) :
  let total_fuel := start_fuel + list_sum (stations.map Prod.snd)
  total_fuel < target →
  min_refuel_stops target start_fuel stations = -1 :=
sorry

theorem min_refuel_stops_stations_ordered (target : Nat) (start_fuel : Nat)
    (stations : List (Nat × Nat)) :
  stations.length > 0 →
  ∀ i : Nat, i < stations.length - 1 →
  (stations.get! i).1 ≤ (stations.get! (i+1)).1 :=
sorry

theorem min_refuel_stops_bound (target : Nat) (start_fuel : Nat)
    (stations : List (Nat × Nat)) :
  let result := min_refuel_stops target start_fuel stations
  result ≠ -1 →
  result ≤ stations.length :=
sorry

theorem min_refuel_stops_empty_stations_sufficient (start_fuel target : Nat) :
  target ≤ start_fuel →
  min_refuel_stops target start_fuel [] = 0 :=
sorry

theorem min_refuel_stops_empty_stations_insufficient (start_fuel target : Nat) :
  start_fuel < target →
  min_refuel_stops target start_fuel [] = -1 :=
sorry

theorem min_refuel_stops_zero_start_fuel (target : Nat) (stations : List (Nat × Nat)) :
  min_refuel_stops target 0 stations = -1 :=
sorry
-- </vc-theorems>