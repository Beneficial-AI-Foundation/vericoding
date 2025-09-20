-- <vc-preamble>
structure FormatResult where
  isStartF : Bool
  containsAssign : Bool

def checkFormat (s : String) : FormatResult :=
  { isStartF := s.data.head? = some 'f',
    containsAssign := s.data.contains '=' }
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculateSequences : List Int → List String :=
sorry

def extractValue (s : String) : String :=
sorry

def extractNumber (s : String) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem list_format_properties {inputs : List Int} :
  let result := calculateSequences inputs
  ∀ x ∈ result,
    let fmt := checkFormat x
    fmt.isStartF ∧ fmt.containsAssign :=
sorry

theorem value_format_properties {inputs : List Int} :
  let result := calculateSequences inputs
  ∀ x ∈ result,
    let n := extractNumber x
    let val := extractValue x
    (n ≥ 5 ∨ n ≤ -51 → val = "MAGNA NIMIS!") ∧
    (n ≤ 3 → val.data.contains '.') :=
sorry

theorem order_matches_reversed {inputs : List Int} :
  let result := calculateSequences inputs
  let nums := result.map extractNumber
  nums = inputs.reverse :=
sorry

theorem known_values {inputs : List Int} (h : inputs.length > 0) :
  let result := calculateSequences inputs
  ∀ x ∈ result,
    let n := extractNumber x
    let val := extractValue x
    (n = 0 → val = "0.00") ∧
    (n = 1 → val = "6.00") ∧
    (n = -1 → val = "-4.00") :=
sorry
-- </vc-theorems>