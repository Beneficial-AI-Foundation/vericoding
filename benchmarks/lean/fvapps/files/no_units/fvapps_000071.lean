-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_beautiful_array (n k : Nat) (a : List Nat) : List Nat := sorry

def countDistinct (l : List Nat) : Nat :=
  (l.foldl (fun acc x => if x ∈ acc then acc else x::acc) []).length
-- </vc-definitions>

-- <vc-theorems>
theorem beautiful_array_properties 
  (n k : Nat) (a : List Nat)
  (hn : n > 0) (hk : k > 0) (hnk : n ≤ 10) (hk10 : k ≤ 10)
  (ha_bounds : ∀ x ∈ a, x ≥ 1 ∧ x ≤ 10)
  (ha_nonempty : a.length > 0)
  (ha_size : a.length ≤ 20) :
  let result := solve_beautiful_array n k a
  match result with
  | [] => countDistinct a > k
  | result => (
    result.length = n * k ∧
    (∀ x ∈ a, x ∈ result) ∧
    countDistinct result ≤ k ∧
    ∀ i, i < n → 
      result.take k = (result.drop (i*k)).take k
  )
  :=
sorry

theorem edge_case_k_one
  (a : List Nat)
  (ha_bounds : ∀ x ∈ a, x ≥ 1 ∧ x ≤ 10)
  (ha_nonempty : a.length > 0)
  (ha_size : a.length ≤ 20) :
  let result := solve_beautiful_array 1 1 a
  match result with 
  | [] => countDistinct a > 1
  | _ => countDistinct a ≤ 1
  :=
sorry

theorem edge_case_k_equals_unique
  (a : List Nat)
  (ha_bounds : ∀ x ∈ a, x ≥ 1 ∧ x ≤ 10)
  (ha_nonempty : a.length > 0)
  (ha_size : a.length ≤ 20) :
  let k := countDistinct a
  solve_beautiful_array 1 k a ≠ []
  :=
sorry
-- </vc-theorems>