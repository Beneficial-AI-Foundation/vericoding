-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_permutation_with_prefix_products (n : Nat) : List Nat :=
sorry

def is_prime (n : Nat) : Bool :=
sorry

def check_prefix_products (result : List Nat) (n : Nat) : Bool :=
sorry

def is_valid_permutation (result : List Nat) (n : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_properties (n : Nat) (h : n ≥ 2) :
  let result := find_permutation_with_prefix_products n
  result.length > 0 →
    result.length = n ∧
    result.head? = some 1 ∧
    result.getLast? = some n ∧
    is_valid_permutation result n ∧
    check_prefix_products result n ∧
    (is_prime n ∨ n = 4) :=
sorry

theorem output_properties_empty (n : Nat) (h : n ≥ 2) :
  let result := find_permutation_with_prefix_products n
  result.length = 0 →
    ¬is_prime n ∧ n ≠ 4 :=
sorry

theorem prime_numbers_have_solution (n : Nat) (h : is_prime n) :
  let result := find_permutation_with_prefix_products n
  result.length = n ∧
  check_prefix_products result n :=
sorry

theorem composite_numbers_have_no_solution (n : Nat) (h1 : n ≥ 6) (h2 : ¬is_prime n) (h3 : n ≠ 4) :
  (find_permutation_with_prefix_products n).length = 0 :=
sorry

theorem special_case_four :
  find_permutation_with_prefix_products 4 = [1, 3, 2, 4] ∧
  check_prefix_products [1, 3, 2, 4] 4 :=
sorry
-- </vc-theorems>