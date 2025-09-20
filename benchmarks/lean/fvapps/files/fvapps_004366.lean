-- <vc-preamble>
def bitLength (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def number_increasing (n : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem impossible_values_2 : number_increasing 2 = false :=
sorry

theorem impossible_values_4 : number_increasing 4 = false :=
sorry

theorem impossible_values_7 : number_increasing 7 = false :=
sorry

theorem impossible_values_12 : number_increasing 12 = false :=
sorry

theorem impossible_values_17 : number_increasing 17 = false :=
sorry

theorem impossible_values_22 : number_increasing 22 = false :=
sorry

theorem multiples_of_five (n : Nat) (h₁ : n > 1) (h₂ : n % 5 = 0) :
  number_increasing n = false :=
sorry

theorem start_point :
  number_increasing 1 = true :=
sorry

theorem multiples_of_three_reachable (n : Nat) (h₁ : n > 1)
  (h₂ : n = 3^(bitLength (bitLength (n - 1)))) :
  number_increasing n = true :=
sorry
-- </vc-theorems>