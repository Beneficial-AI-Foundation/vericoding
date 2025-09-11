-- <vc-preamble>
def amort (rate : Float) (bal : Int) (term : Int) (num_payments : Int) : String := sorry

structure AmortValues where
  num_payment : Int
  payment : Int
  principal : Int
  interest : Int
  balance : Float

/- Helper function to extract numeric values from amortization string output -/

def extractValuesFromString (s : String) : AmortValues := sorry

/- Helper function to check if string matches expected pattern -/
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def matchesPattern (s : String) : Bool := sorry

theorem amort_output_format (rate : Float) (bal : Int) (term : Int) (num_payments : Int)
  (h1 : rate ≥ 0.1) (h2 : rate ≤ 30.0)
  (h3 : bal ≥ 1000) (h4 : bal ≤ 1000000)
  (h5 : term ≥ 12) (h6 : term ≤ 360)
  (h7 : num_payments ≥ 1) (h8 : num_payments ≤ term) :
  let result := amort rate bal term num_payments
  let values := extractValuesFromString result
  (matchesPattern result) ∧ 
  (values.num_payment = num_payments) ∧
  (values.payment ≥ 0) ∧
  (values.principal ≥ 0) ∧
  (values.interest ≥ 0) ∧
  (Int.natAbs (values.principal + values.interest - values.payment) ≤ 1) := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded