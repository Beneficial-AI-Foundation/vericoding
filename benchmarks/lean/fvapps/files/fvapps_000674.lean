-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def factorial (n : Nat) : Nat :=
  sorry

def calculate_factorials (nums : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_list_factorial :
  calculate_factorials [] = [] :=
sorry

theorem factorial_zero :
  calculate_factorials [0] = [1] :=
sorry

theorem factorial_one :
  calculate_factorials [1] = [1] :=
sorry
-- </vc-theorems>