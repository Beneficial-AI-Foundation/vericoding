-- <vc-preamble>
def COLOR_MAP : List (String × Nat) := [
  ("black", 0), ("brown", 1), ("red", 2), ("orange", 3), ("yellow", 4),
  ("green", 5), ("blue", 6), ("violet", 7), ("gray", 8), ("white", 9)
]
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def decode_resistor_colors (bands : String) : String :=
sorry

def String.toFloat (s : String) : Float :=
sorry

def String.containsString (s : String) (substr : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem resistor_color_format
  (first_band second_band multiplier : String)
  (tolerance : Option String)
  (h1 : first_band ∈ (COLOR_MAP.map (·.1)))
  (h2 : second_band ∈ (COLOR_MAP.map (·.1)))
  (h3 : multiplier ∈ (COLOR_MAP.map (·.1)))
  (h4 : tolerance.getD "" ∈ ["", "gold", "silver"]) :
  let result := decode_resistor_colors (s!"{first_band} {second_band} {multiplier} {tolerance.getD ""}".trim)
  (result.containsString " ohms, ") ∧
  (result.endsWith "%") ∧
  (result.containsString "" ∨ result.containsString "k" ∨ result.containsString "M") :=
sorry

theorem base_value_calculation
  (first_band second_band multiplier : String)
  (h1 : first_band ∈ ["black", "brown"])
  (h2 : second_band ∈ ["black", "brown"])
  (h3 : multiplier = "black") :
  let result := decode_resistor_colors (s!"{first_band} {second_band} {multiplier}")
  let value := String.toFloat ((result.splitOn " ").head!)
  let expected :=
    match COLOR_MAP.find? (·.1 = first_band), COLOR_MAP.find? (·.1 = second_band) with
    | some (_, n1), some (_, n2) => Float.ofNat (n1 * 10 + n2)
    | _, _ => 0.0
  value = expected :=
sorry
-- </vc-theorems>