-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def make_upper_case (s : String) : String := sorry

theorem make_upper_case_idempotent (s : String) :
  make_upper_case (make_upper_case s) = make_upper_case s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem make_upper_case_is_upper (s : String) :
  String.toUpper (make_upper_case s) = make_upper_case s := sorry

theorem make_upper_case_upper_lower_chain (s : String) :
  String.toUpper (String.toLower (make_upper_case s)) = make_upper_case s := sorry
-- </vc-theorems>