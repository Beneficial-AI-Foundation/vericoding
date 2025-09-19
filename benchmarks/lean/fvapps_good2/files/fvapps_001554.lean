-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def primeFactors (n : Nat) : List Nat :=
  sorry

def find_spec_prod_part (n : Nat) (mode : String) : String ⊕ (List Nat × Nat) :=
  sorry

def is_prime (n : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem prime_find_spec_prod_part (n : Nat) (h : n ≥ 2) :
  is_prime n = true →
  find_spec_prod_part n "max" = Sum.inl "It is a prime number" ∧
  find_spec_prod_part n "min" = Sum.inl "It is a prime number" :=
sorry

theorem partition_product_equals_input (n : Nat) (h1 : n ≥ 4) (h2 : is_prime n = false) :
  match find_spec_prod_part n "max", find_spec_prod_part n "min" with
  | Sum.inr (max_parts, _), Sum.inr (min_parts, _) =>
    (max_parts.foldl Nat.mul 1 = n) ∧
    (min_parts.foldl Nat.mul 1 = n)
  | _, _ => False
  :=
sorry

theorem min_max_relationship (n : Nat) (h1 : n ≥ 4) (h2 : is_prime n = false) :
  match find_spec_prod_part n "max", find_spec_prod_part n "min" with
  | Sum.inr (_, max_score), Sum.inr (_, min_score) => max_score ≥ min_score
  | _, _ => False
  :=
sorry
-- </vc-theorems>