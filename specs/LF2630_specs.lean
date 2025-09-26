-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sol_equa (n : Nat) : List (List Nat) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sol_equa_well_formed (n : Nat) :
  ∀ result : List (List Nat),
    result = sol_equa n →
    (∀ pair ∈ result, pair.length = 2) :=
sorry

theorem sol_equa_satisfies_equation (n : Nat) :
  ∀ result : List (List Nat),
    result = sol_equa n →
    ∀ pair ∈ result,
      pair.get! 0 * pair.get! 0 - 4 * pair.get! 1 * pair.get! 1 = n :=
sorry

theorem sol_equa_positive_values (n : Nat) :
  ∀ result : List (List Nat),
    result = sol_equa n →
    ∀ pair ∈ result,
      pair.get! 0 > 0 ∧ pair.get! 1 ≥ 0 :=
sorry

theorem sol_equa_ordered (n : Nat) :
  ∀ result : List (List Nat),
    result = sol_equa n →
    ∀ i < result.length - 1,
      (result.get! i).get! 0 > (result.get! (i+1)).get! 0 :=
sorry

theorem sol_equa_90002_empty :
  sol_equa 90002 = [] :=
sorry

theorem sol_equa_5_single :
  sol_equa 5 = [[3,1]] :=
sorry
-- </vc-theorems>