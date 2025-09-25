-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def prod_int_part (n: Nat) (min: Nat := 2) : Nat × List Nat :=
sorry

def isPrime (n: Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem prod_int_part_output_structure (n: Nat) (h: n ≥ 2) :
  let result := prod_int_part n
  result.1 ≥ 0 ∧ result.2.all (λ x => x ≥ 2) :=
sorry

theorem prime_numbers_return_empty (n: Nat) (h: n ≥ 2) :
  isPrime n → prod_int_part n = (0, []) :=
sorry

theorem factors_multiply_to_input (n: Nat) (h: n ≥ 2) :
  let result := prod_int_part n
  result.2 ≠ [] → result.2.foldl (·*·) 1 = n :=
sorry

theorem factors_are_ordered (n: Nat) (h: n ≥ 2) :
  let result := prod_int_part n
  result.2.length > 1 →
  ∀ i, i < result.2.length - 1 →
  result.2[i]! ≤ result.2[i+1]! :=
sorry

theorem min_parameter_respects_boundary (n min: Nat) (h1: n ≥ 2) (h2: min ≥ 2) :
  let result := prod_int_part n min
  result.2.all (λ x => x ≥ min) :=
sorry
-- </vc-theorems>