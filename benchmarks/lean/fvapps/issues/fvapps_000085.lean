-- <vc-preamble>
def List.sum : List Nat → Nat 
| [] => 0
| x::xs => x + (sum xs)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_alternating_array (n: Nat) (arr: List Nat) : Nat × List Nat := sorry

theorem solve_alternating_array_size_constraints {n: Nat} {arr: List Nat} 
  (h1: n > 0) (h2: ∀ x ∈ arr, x ≤ 1) :
  let (size, result) := solve_alternating_array n arr
  (size = result.length ∧ size ≤ n ∧ size ≥ n/2) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_alternating_array_result_constraints {n: Nat} {arr: List Nat}
  (h1: n > 0) (h2: ∀ x ∈ arr, x ≤ 1) :
  let (_, result) := solve_alternating_array n arr
  (∀ x ∈ result, x ≤ 1) := sorry

theorem solve_alternating_array_all_zeros {n: Nat} {arr: List Nat}
  (h1: n > 0) (h2: ∀ x ∈ arr, x ≤ 1) 
  (h3: List.sum arr ≤ n/2) :
  let (_, result) := solve_alternating_array n arr
  (∀ x ∈ result, x = 0) := sorry

theorem solve_alternating_array_all_ones {n: Nat} {arr: List Nat}
  (h1: n > 0) (h2: ∀ x ∈ arr, x ≤ 1)
  (h3: List.sum arr > n/2) :
  let (_, result) := solve_alternating_array n arr
  (∀ x ∈ result, x = 1) := sorry

theorem solve_alternating_array_extreme_cases {n: Nat} 
  (h1: n > 0) :
  let (size1, _) := solve_alternating_array n (List.replicate n 0)
  let (size2, _) := solve_alternating_array n (List.replicate n 1)
  (n/2 ≤ size1 ∧ size1 ≤ n/2 + 1 ∧ 
   n/2 ≤ size2 ∧ size2 ≤ n/2 + 1) := sorry
-- </vc-theorems>