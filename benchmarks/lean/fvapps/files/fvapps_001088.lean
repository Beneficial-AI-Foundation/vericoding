-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_cupcakes (rows cols : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cupcakes_non_negative (rows cols : Nat) : 
  calculate_cupcakes rows cols ≥ 0 ∧ calculate_cupcakes rows cols = rows * cols :=
  sorry

theorem cupcakes_positive (rows cols : Nat) (h1 : rows > 0) (h2 : cols > 0) :
  calculate_cupcakes rows cols > 0 ∧ 
  calculate_cupcakes rows cols = rows * cols ∧
  calculate_cupcakes rows cols ≥ max rows cols :=
  sorry

theorem cupcakes_commutative (rows cols : Nat) :
  calculate_cupcakes rows cols = calculate_cupcakes cols rows :=
  sorry

theorem cupcakes_zero_cases (n : Nat) :
  calculate_cupcakes 0 n = 0 ∧ 
  calculate_cupcakes n 0 = 0 ∧
  calculate_cupcakes 0 0 = 0 :=
  sorry
-- </vc-theorems>