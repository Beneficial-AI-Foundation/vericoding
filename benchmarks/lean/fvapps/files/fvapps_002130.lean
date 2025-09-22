-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_trip_sizes (n m k : Nat) (friendships : List (Nat × Nat)) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_trip_sizes_basic_properties
  (n m k : Nat)
  (friendships : List (Nat × Nat))
  (h1 : n ≥ 2)
  (h2 : k < n)
  (h3 : m ≥ 1)
  (h4 : ∀ (p : Nat × Nat), p ∈ friendships → p.1 ≤ n ∧ p.2 ≤ n)
  (h5 : ∀ (p : Nat × Nat), p ∈ friendships → p.1 ≠ p.2)
  : (List.length (max_trip_sizes n m k friendships) = m) ∧ 
    (∀ x ∈ max_trip_sizes n m k friendships, 0 ≤ x ∧ x ≤ n) ∧
    (∀ i, i + 1 < List.length (max_trip_sizes n m k friendships) →
      List.get! (max_trip_sizes n m k friendships) i ≤ 
      List.get! (max_trip_sizes n m k friendships) (i + 1)) :=
sorry

theorem max_trip_sizes_degree_bound
  (n m k : Nat)
  (friendships : List (Nat × Nat))
  (h1 : n ≥ 2)
  (h2 : k < n)
  (h3 : m ≥ 1)
  (h4 : ∀ (p : Nat × Nat), p ∈ friendships → p.1 ≤ n ∧ p.2 ≤ n)
  (h5 : ∀ (p : Nat × Nat), p ∈ friendships → p.1 ≠ p.2)
  : ∀ x ∈ max_trip_sizes n m k friendships, 
    x ≤ (List.length (List.filter 
      (λ d => d ≥ k) 
      (friendships.foldl 
        (λ acc p => 
          let acc' := acc.set (p.1 - 1) ((acc.get! (p.1 - 1)) + 1)
          acc'.set (p.2 - 1) ((acc'.get! (p.2 - 1)) + 1)) 
        (List.replicate n 0)))) :=
sorry
-- </vc-theorems>