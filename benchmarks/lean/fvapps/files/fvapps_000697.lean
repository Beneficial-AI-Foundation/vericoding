-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def leastPrimeDivisors (n : Nat) : List Nat :=
  sorry

def dividing_machine (n m : Nat) (arr : List Nat) (ops : List (List Nat)) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem least_prime_divisors_are_prime (n : Nat) :
  (∀ p ∈ leastPrimeDivisors n, p > 1) ∧
  (∀ p ∈ leastPrimeDivisors n, ∀ i : Nat, 2 ≤ i ∧ i * i ≤ p → p % i ≠ 0) :=
sorry

theorem dividing_machine_valid_result {n m : Nat} {arr : List Nat} {ops : List (List Nat)}
  (h_ops : ∀ op ∈ ops, op.length = 3 ∧
          (op.get! 0 < 2 ∧ 1 ≤ op.get! 1 ∧ op.get! 1 ≤ op.get! 2 ∧ op.get! 2 ≤ n)) :
  (dividing_machine n m arr ops).length = (ops.filter (fun op => op.get! 0 = 1)).length ∧
  ∀ x ∈ dividing_machine n m arr ops, x ≥ 1 :=
sorry

theorem single_number_valid {x : Nat} (h : x ≥ 1) :
  let result := dividing_machine 1 1 [x] [[1,1,1]]
  result.length = 1 ∧ result.get! 0 ≥ 1 :=
sorry
-- </vc-theorems>