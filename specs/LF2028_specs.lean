-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_array_destroy (n : Nat) (nums : List Nat) (destroy_order : List Nat) : List Nat := sorry

def list_sum (l : List Nat) : Nat :=
  match l with 
  | [] => 0
  | x::xs => x + list_sum xs
-- </vc-definitions>

-- <vc-theorems>
theorem solve_array_destroy_output_valid 
  (n : Nat) (nums destroy_order : List Nat)
  (h1 : n > 0) (h2 : n ≤ 100)
  (h3 : ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 1000)
  (h4 : destroy_order.length = n)
  (h5 : ∀ x ∈ destroy_order, 1 ≤ x ∧ x ≤ n)
  (h6 : ∀ i j, i < j → i < destroy_order.length → j < destroy_order.length → 
        destroy_order.get! i ≠ destroy_order.get! j) :
  let result := solve_array_destroy n nums destroy_order
  result.length = n ∧ 
  (result.length > 0 → result.get? (result.length - 1) = some 0) ∧
  (∀ x ∈ result, x ≥ 0) ∧
  (∀ i < result.length - 1, match result.get? i, result.get? (i+1) with
    | some x, some y => x ≥ y
    | _, _ => True) := sorry

theorem solve_array_destroy_adjacent_valid
  (n : Nat) (nums destroy_order : List Nat)
  (h1 : n ≥ 2) (h2 : n ≤ 20)
  (h3 : ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 100)
  (h4 : destroy_order.length = n)
  (h5 : ∀ x ∈ destroy_order, 1 ≤ x ∧ x ≤ n)
  (h6 : ∀ i j, i < j → i < destroy_order.length → j < destroy_order.length → 
        destroy_order.get! i ≠ destroy_order.get! j) :
  let result := solve_array_destroy n nums destroy_order
  result.length = n ∧
  (result.length > 0 → result.get? (result.length - 1) = some 0) := sorry

theorem solve_array_destroy_max_bound
  (n : Nat) (nums destroy_order : List Nat)
  (h1 : n > 0) (h2 : n ≤ 50)
  (h3 : ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 1000)
  (h4 : destroy_order.length = n)
  (h5 : ∀ x ∈ destroy_order, 1 ≤ x ∧ x ≤ n)
  (h6 : ∀ i j, i < j → i < destroy_order.length → j < destroy_order.length → 
        destroy_order.get! i ≠ destroy_order.get! j) :
  let result := solve_array_destroy n nums destroy_order
  result.length = n ∧
  ∀ x ∈ result, x ≤ list_sum nums := sorry
-- </vc-theorems>