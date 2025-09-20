-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_DNA (s1 s2 : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_DNA_symmetric (s1 s2 : String) :
  check_DNA s1 s2 = check_DNA s2 s1 :=
sorry

theorem check_DNA_empty (s : String) :
  check_DNA s "" = true ∧ check_DNA "" s = true :=
sorry

theorem check_DNA_basic_complement :
  check_DNA "ATGCTACG" "CGTAGCAT" = true :=
sorry
-- </vc-theorems>