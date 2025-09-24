-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def london_city_hacker (journey : List (Unit ⊕ Unit)) : String := sorry

def is_valid_fare_string (fare : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem journey_fare_is_valid {journey : List (Unit ⊕ Unit)} :
  is_valid_fare_string (london_city_hacker journey) := sorry

theorem journey_fare_calculation {journey : List (Unit ⊕ Unit)} :
  ∃ total : Float,
  london_city_hacker journey = toString ("£" ++ toString total) ∧
  total = journey.foldr
    (fun x acc => match x with
      | Sum.inr _ => acc + 2.40
      | Sum.inl _ => match journey with
        | _::next::_ => if next = Sum.inl () then acc + 0.75 else acc + 1.50  
        | _ => acc + 1.50) 0 := sorry

theorem all_bus_journey_calculation {buses : List Unit} :
  let busCount := buses.length
  london_city_hacker (buses.map Sum.inl) = 
  toString ("£" ++ toString ((Float.ofNat busCount / 2) * 1.50 + 
    (Float.ofNat (busCount % 2)) * 1.50)) := sorry

theorem all_tube_journey_calculation {tubes : List Unit} :
  london_city_hacker (tubes.map Sum.inr) = 
  toString ("£" ++ toString (Float.ofNat tubes.length * 2.40)) := sorry
-- </vc-theorems>