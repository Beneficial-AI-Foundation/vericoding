-- <vc-preamble>
def countChar (s : String) (c : Char) : Nat := 
  (s.data.filter (· = c)).length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bumps (road : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bumps_returns_valid_output (road : String) :
  (bumps road = "Woohoo!" ∨ bumps road = "Car Dead") ∧
  (bumps road = "Woohoo!" ↔ countChar road 'n' ≤ 15) :=
sorry

theorem no_bumps_woohoo (road : String) :
  (∀ c ∈ road.toList, c = '_') →
  bumps road = "Woohoo!" :=
sorry

theorem too_many_bumps_dead (road : String) :
  (∀ c ∈ road.toList, c = 'n') →
  road.length ≥ 16 →
  bumps road = "Car Dead" :=
sorry

theorem empty_road_woohoo :
  bumps "" = "Woohoo!" :=
sorry

theorem edge_case_fifteen :
  let nStr15 := String.mk (List.replicate 15 'n')
  let nStr16 := String.mk (List.replicate 16 'n')
  bumps nStr15 = "Woohoo!" ∧
  bumps nStr16 = "Car Dead" :=
sorry
-- </vc-theorems>