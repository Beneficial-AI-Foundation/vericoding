-- <vc-helpers>
-- </vc-helpers>

def solution (toCurrency : String) (values : List Float) : List String := sorry

def stringToFloat (s : String) : Float := sorry

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

/-
info: ['$1.15', '$94.65']
-/
-- #guard_msgs in
-- #eval solution "USD" [1.01, 83.29]

/-
info: ['96.32€', '563.47€']
-/
-- #guard_msgs in
-- #eval solution "EUR" [109.45, 640.31]

/-
info: ['$0.00', '$0.00', '$0.00']
-/
-- #guard_msgs in
-- #eval solution "USD" [0, 0, 0]

-- Apps difficulty: introductory
-- Assurance level: unguarded