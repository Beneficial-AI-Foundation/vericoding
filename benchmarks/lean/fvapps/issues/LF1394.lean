-- <vc-preamble>
def LighthouseConfig := Nat × Direction

def solve_lighthouse_placement (coords : List IslandCoord) : List LighthouseConfig :=
  sorry

def format_output (configs : List LighthouseConfig) : List String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def direction_to_string : Direction → String
  | Direction.NE => "NE"
  | Direction.SE => "SE"
  | Direction.SW => "SW"
  | Direction.NW => "NW"
-- </vc-definitions>

-- <vc-theorems>
theorem lighthouse_placement_valid {coords : List IslandCoord} :
  let result := solve_lighthouse_placement coords
  (∀ x ∈ result, x.1 ≤ coords.length) ∧ 
  (1 ≤ result.length ∧ result.length ≤ 2) := 
sorry

theorem format_output_valid {coords : List IslandCoord} :
  let lighthouse_configs := solve_lighthouse_placement coords
  let result := format_output lighthouse_configs
  (result.head? = some (toString lighthouse_configs.length)) ∧
  (result.length = lighthouse_configs.length + 1) :=
sorry
-- </vc-theorems>