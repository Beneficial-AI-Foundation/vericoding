-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def spreadsheet (s : String) : String :=
sorry

def is_valid_a1 (s : String) : Bool :=
sorry

def is_valid_r1c1 (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem a1_conversion {s : String} (h : is_valid_a1 s = true) :
  is_valid_r1c1 (spreadsheet s) = true ∧
  spreadsheet (spreadsheet s) = s :=
sorry

theorem r1c1_conversion {s : String} (h : is_valid_r1c1 s = true) :
  is_valid_a1 (spreadsheet s) = true ∧
  spreadsheet (spreadsheet s) = s :=
sorry

theorem conversion_idempotent_a1 {s : String} (h : is_valid_a1 s = true) :
  spreadsheet (spreadsheet s) = s :=
sorry

theorem conversion_idempotent_r1c1 {s : String} (h : is_valid_r1c1 s = true) :
  spreadsheet (spreadsheet s) = s :=
sorry
-- </vc-theorems>