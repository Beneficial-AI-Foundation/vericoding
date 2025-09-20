-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def n_linear (multipliers : List Nat) (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem n_linear_positive (multipliers : List Nat) (n : Nat)
  (h1 : multipliers.length > 0) 
  (h2 : ∀ x ∈ multipliers, x ≥ 2)
  (h3 : n ≥ 1) :
  n_linear multipliers n > 0 :=
sorry

theorem n_linear_monotonic (multipliers : List Nat) (n : Nat)
  (h1 : multipliers.length > 0)
  (h2 : ∀ x ∈ multipliers, x ≥ 2) 
  (h3 : n > 1) :
  n_linear multipliers (n-1) < n_linear multipliers n :=
sorry

theorem n_linear_strictly_increasing (multipliers : List Nat)
  (h1 : multipliers.length > 0)
  (h2 : ∀ x ∈ multipliers, x ≥ 2) :
  ∀ i, i < 2 → n_linear multipliers (i+1) < n_linear multipliers (i+2) :=
sorry
-- </vc-theorems>