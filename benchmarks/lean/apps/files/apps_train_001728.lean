-- <vc-helpers>
-- </vc-helpers>

def permutational_primes (n_max k_perms : Nat) : List Nat := sorry

-- Type signature property

theorem perm_primes_returns_three_nats (n_max k_perms : Nat) : 
  let result := permutational_primes n_max k_perms;
  result.length = 3
  ∧ result.all (λ x => x ≥ 0) := sorry

-- Count non-negative property  

theorem perm_primes_count_nonneg (n_max k_perms : Nat) :
  let result := permutational_primes n_max k_perms;
  (result.get! 0) ≥ 0 := sorry

-- Zero count implies zero min/max property

theorem perm_primes_zero_count (n_max k_perms : Nat) :
  let result := permutational_primes n_max k_perms;
  (result.get! 0 = 0) →
  (result.get! 1 = 0 ∧ result.get! 2 = 0) := sorry

-- Valid count implies valid min/max property  

theorem perm_primes_valid_bounds (n_max k_perms : Nat) :
  let result := permutational_primes n_max k_perms;
  (result.get! 0 > 0) →
  (result.get! 1 > 1 
   ∧ result.get! 2 > 1
   ∧ result.get! 1 ≤ result.get! 2
   ∧ result.get! 1 < n_max
   ∧ result.get! 2 < n_max) := sorry

/-
info: [3, 149, 379]
-/
-- #guard_msgs in
-- #eval permutational_primes 1000 3

/-
info: [9, 113, 389]
-/
-- #guard_msgs in
-- #eval permutational_primes 1000 2

/-
info: [34, 13, 797]
-/
-- #guard_msgs in
-- #eval permutational_primes 1000 1

-- Apps difficulty: interview
-- Assurance level: unguarded