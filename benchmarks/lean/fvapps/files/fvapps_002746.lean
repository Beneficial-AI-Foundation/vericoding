-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def champernowne_digit (n: Int) : Option Int := 
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_positive_inputs {n: Int} (hn: n ≤ 0) :
  champernowne_digit n = none := by sorry

theorem digit_in_range {n: Int} (hn: n > 0) :
  let result := champernowne_digit n
  ∀ d, result = some d → 0 ≤ d ∧ d ≤ 9 := by sorry 

theorem first_ten_digits :
  champernowne_digit 1 = some 0 ∧
  champernowne_digit 2 = some 1 ∧ 
  champernowne_digit 3 = some 2 ∧
  champernowne_digit 4 = some 3 ∧
  champernowne_digit 5 = some 4 ∧
  champernowne_digit 6 = some 5 ∧
  champernowne_digit 7 = some 6 ∧
  champernowne_digit 8 = some 7 ∧
  champernowne_digit 9 = some 8 ∧
  champernowne_digit 10 = some 9 := by sorry
-- </vc-theorems>