-- <vc-preamble>
def isqrt (n : Nat) : Nat := sorry 

def isPrime (p : Nat) : Bool := sorry

structure PrimeFactor where
  prime : Nat
  power : Nat
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def factorize (n : Nat) : List PrimeFactor := sorry

theorem isqrt_upper_bound (n : Nat) (h : n > 0) : 
  let r := isqrt n
  r * r ≤ n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isqrt_next_exceeds (n : Nat) (h : n > 0) :
  let r := isqrt n 
  (r + 1) * (r + 1) > n := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval trailing_zeros 15 10

/-
info: 4
-/
-- #guard_msgs in
-- #eval trailing_zeros 7 2

/-
info: 7
-/
-- #guard_msgs in
-- #eval trailing_zeros 30 10
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible