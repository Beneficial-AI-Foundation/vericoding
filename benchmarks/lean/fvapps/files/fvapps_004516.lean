-- <vc-preamble>
def List.prod : List Nat → Nat 
  | [] => 1
  | x :: xs => x * List.prod xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_find_num (primes: List Nat) (limit: Nat) : Option (Nat × Nat) := sorry

theorem count_find_num_basic_props {primes: List Nat} {limit: Nat} :
  match count_find_num primes limit with
  | none => ∀ p ∈ primes, p ≥ 2 → (List.prod primes > limit) 
  | some (count, max_val) => 
      (∀ p ∈ primes, p ≥ 2) →
      List.prod primes ≤ limit ∧ 
      max_val ≤ limit ∧
      count ≥ 1 ∧
      max_val ≥ List.prod primes
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_find_num_divisible {primes: List Nat} {limit: Nat} :
  match count_find_num primes limit with
  | none => True
  | some (count, max_val) =>
      ∀ p ∈ primes, max_val % p = 0
  := sorry

theorem count_find_num_edge_cases_1 :
  count_find_num [2] 1 = none := sorry

theorem count_find_num_edge_cases_2 :
  count_find_num [2] 2 = some (1, 2) := sorry

theorem count_find_num_edge_cases_3 :
  count_find_num [2, 3] 5 = none := sorry
-- </vc-theorems>