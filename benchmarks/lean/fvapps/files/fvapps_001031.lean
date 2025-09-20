-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_remainders (cases : List String) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_remainders_length (cases : List String) :
  (find_remainders cases).length = cases.length :=
sorry

theorem find_remainders_correct (test_case : String) (a b : Nat) (h : test_case = s!"{a} {b}") :
  b > 0 → a > 0 →
  find_remainders [test_case] = [a % b] :=
sorry

theorem find_remainders_bounds (test_case : String) (a b : Nat) (h : test_case = s!"{a} {b}") :
  b > 0 → a > 0 →
  let r := (find_remainders [test_case]).head!
  0 ≤ r ∧ r < b :=
sorry

theorem find_remainders_div_by_one (a : Nat) (h : a > 0) :
  find_remainders [s!"{a} 1"] = [0] :=
sorry
-- </vc-theorems>