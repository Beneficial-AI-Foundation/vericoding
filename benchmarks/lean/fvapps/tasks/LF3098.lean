-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isLower (c : Char) : Bool :=
sorry

def isUpper (c : Char) : Bool :=
sorry

def tv_remote (s : String) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tv_remote_basic_properties (s : String) : tv_remote s ≥ 0 :=
sorry

theorem tv_remote_empty_string : tv_remote "" = 0 :=
sorry

theorem tv_remote_case_sensitivity (s : String) :
  s ≠ "" → tv_remote (s.map Char.toUpper) ≥ tv_remote (s.map Char.toLower) :=
sorry
-- </vc-theorems>