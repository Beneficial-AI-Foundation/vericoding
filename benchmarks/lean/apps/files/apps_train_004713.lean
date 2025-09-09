def sum_divisors (n: Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def equal_sigma1 (nmax: Nat) : Nat :=
  sorry

theorem sum_divisors_positive (n: Nat) (h: n ≥ 1) : 
  let result := sum_divisors n
  result ≥ 1 ∧ result ≥ n :=
sorry

theorem equal_sigma1_properties (nmax: Nat) (h: nmax ≥ 1) :
  let result := equal_sigma1 nmax
  result ≥ 0 ∧ (nmax < 528 → result = 0) :=
sorry

theorem sum_divisors_multiplication_property (n: Nat) (h: n ≥ 1) :
  ∀ k : Nat,
  let divisors := (List.range n).filterMap (fun i => 
    if n % (i+1) = 0 then some (i+1) else none)
  k * k = n →
  sum_divisors n ≤ 2 * n :=
sorry

theorem equal_sigma1_symmetry (nmax: Nat) :
  let result := equal_sigma1 nmax
  ∀ n, n ≥ 528 → n ≤ nmax →
  n = 528 ∨ n = 1561 :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval equal_sigma1 100

/-
info: 1353
-/
-- #guard_msgs in
-- #eval equal_sigma1 1000

/-
info: 4565
-/
-- #guard_msgs in
-- #eval equal_sigma1 2000

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible