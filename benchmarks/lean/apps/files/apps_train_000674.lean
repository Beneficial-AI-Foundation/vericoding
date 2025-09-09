def factorial (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def calculate_factorials (nums : List Nat) : List Nat :=
  sorry

theorem empty_list_factorial :
  calculate_factorials [] = [] :=
sorry

theorem factorial_zero :
  calculate_factorials [0] = [1] :=
sorry

theorem factorial_one :
  calculate_factorials [1] = [1] :=
sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible