-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def convertToExcelTitle (n : Nat) : String := sorry

def colNumFromStr (s : String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem convert_to_excel_title_properties (n : Nat) 
  (h1 : n > 0) (h2 : n ≤ 1000000) :
  let result := convertToExcelTitle n
  -- Result is nonempty
  String.length result > 0 ∧ 
  -- Result converts back to original number
  colNumFromStr result = n :=
sorry

theorem single_letter_cases (n : Nat)
  (h1 : n > 0) (h2 : n ≤ 26) :
  let result := convertToExcelTitle n
  String.length result = 1 :=
sorry

theorem edge_cases :
  convertToExcelTitle 1 = "A" ∧
  convertToExcelTitle 26 = "Z" ∧ 
  convertToExcelTitle 27 = "AA" :=
sorry
-- </vc-theorems>