-- <vc-preamble>
def compute_super_factor_sum (n : Nat) : Nat := sorry

def is_prime (n : Nat) : Bool := sorry

def list_product : List Nat → Nat 
  | [] => 1
  | x :: xs => x * list_product xs
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + list_sum xs
-- </vc-definitions>

-- <vc-theorems>
theorem compute_super_factor_sum_positive (n : Nat) (h : n ≥ 2) :
  compute_super_factor_sum n > 0 := sorry

theorem compute_super_factor_sum_primes (n : Nat) (h1 : n ≥ 2) (h2 : is_prime n = true) : 
  compute_super_factor_sum n = n := sorry

theorem compute_super_factor_sum_multiplicative (a b : Nat) (h1 : a ≥ 1) (h2 : b ≥ 1) :
  compute_super_factor_sum (a * b) ≥ min (compute_super_factor_sum a) (compute_super_factor_sum b) := sorry

theorem compute_super_factor_sum_product_relation (factors : List Nat) 
  (h1 : ∀ x ∈ factors, x ≥ 2) (h2 : factors.length > 0) :
  compute_super_factor_sum (list_product factors) ≥ 
  list_sum (List.map compute_super_factor_sum (List.filter (fun x => x > 1) factors)) := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval compute_super_factor_sum 6

/-
info: 7
-/
-- #guard_msgs in
-- #eval compute_super_factor_sum 7

/-
info: 7
-/
-- #guard_msgs in
-- #eval compute_super_factor_sum 12
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded