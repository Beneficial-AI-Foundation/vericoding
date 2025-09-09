def isPrime (n : Nat) : Bool :=
  sorry

def getFirstNPrimes (n : Nat) : List Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def numPrimorial (n : Nat) : Nat :=
  sorry

theorem primorial_equals_product_of_first_n_primes (n : Nat) 
  (h : n ≥ 1 ∧ n ≤ 10) : 
  numPrimorial n = (getFirstNPrimes n).foldl (·*·) 1 :=
sorry

theorem primorial_is_strictly_increasing {n : Nat}
  (h1 : n ≥ 1 ∧ n ≤ 10) (h2 : n > 1) :
  numPrimorial n > numPrimorial (n-1) :=
sorry

theorem primorial_is_divisible_by_smaller_primorials {n : Nat}
  (h1 : n ≥ 1 ∧ n ≤ 10) (h2 : n > 1) :
  numPrimorial n % numPrimorial (n-1) = 0 :=
sorry

/-
info: 30
-/
-- #guard_msgs in
-- #eval num_primorial 3

/-
info: 2310
-/
-- #guard_msgs in
-- #eval num_primorial 5

/-
info: 9699690
-/
-- #guard_msgs in
-- #eval num_primorial 8

-- Apps difficulty: introductory
-- Assurance level: guarded