-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solution (toCurrency : String) (values : List Float) : List String := sorry

def stringToFloat (s : String) : Float := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solution_maintains_length (toCurrency : String) (values : List Float) :
  (values.length > 0) → 
  (solution toCurrency values).length = values.length := sorry

theorem solution_uses_correct_usd_symbols (toCurrency : String) (values : List Float) :
  (values.length > 0) →
  (toCurrency = "USD") →
  ∀ x ∈ solution toCurrency values, x.startsWith "$" ∧ ¬(x.contains '€') := sorry

theorem solution_uses_correct_eur_symbols (toCurrency : String) (values : List Float) :
  (values.length > 0) →
  (toCurrency = "EUR") →
  ∀ x ∈ solution toCurrency values, x.endsWith "€" ∧ ¬(x.contains '$') := sorry

theorem solution_has_two_decimals (toCurrency : String) (values : List Float) :
  (values.length > 0) →
  ∀ x ∈ solution toCurrency values,
    (x.contains '.') ∧
    ((x.split (· = '.')).getLast!.replace "€" "").length = 2 := sorry

theorem solution_handles_zero (toCurrency : String) (values : List Float) :
  (values.length > 0) →
  (∀ x ∈ values, x = 0) →
  ∀ y ∈ solution toCurrency values,
    y = (if toCurrency = "USD" then "$0.00" else "0.00€") := sorry

theorem solution_conversion_inverse (toCurrency : String) (value : Float) :
  let otherCurrency := if toCurrency = "USD" then "EUR" else "USD"
  let firstConversion := solution otherCurrency [value]
  let withoutSymbols := (firstConversion[0]!.replace "$" "").replace "€" ""
  let secondConversion := solution toCurrency [stringToFloat withoutSymbols]
  let originalAmount := if toCurrency = "USD" then s!"${value}" else s!"${value}€"
  let finalValue := stringToFloat ((secondConversion[0]!.replace "$" "").replace "€" "")
  let originalValue := stringToFloat ((originalAmount.replace "$" "").replace "€" "")
  (finalValue - originalValue) < 0.01 := sorry
-- </vc-theorems>