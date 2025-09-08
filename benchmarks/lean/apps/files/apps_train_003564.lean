/-
# Task
We know that some numbers can be split into two primes. ie. `5 = 2 + 3, 10 = 3 + 7`. But some numbers are not. ie. `17, 27, 35`, etc.. 

Given a positive integer `n`. Determine whether it can be split into two primes. If yes, return the maximum product of two primes. If not, return `0` instead.

# Input/Output

`[input]` integer `n`

A positive integer. 

`0 ≤ n ≤ 100000`

`[output]` an integer

The possible maximum product of two primes. or return `0` if it's impossible split into two primes.

# Example

For `n = 1`, the output should be `0`.

`1` can not split into two primes

For `n = 4`, the output should be `4`.

`4` can split into two primes `2 and 2`. `2 x 2 = 4`

For `n = 20`, the output should be `91`.

`20` can split into two primes `7 and 13` or `3 and 17`. The maximum product is `7 x 13 = 91`
-/

-- <vc-helpers>
-- </vc-helpers>

def is_prime (n : Nat) : Bool := sorry

def prime_product (n : Nat) : Nat := sorry

theorem prime_positive_factors (n : Nat) (h : n ≥ 2) : 
  is_prime n = true → ∀ i : Nat, 2 ≤ i → i ≤ n^(1/2) → n % i ≠ 0 := sorry

theorem nonpositive_not_prime (n : Nat) :
  n ≤ 1 → is_prime n = false := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval prime_product 5

/-
info: 91
-/
-- #guard_msgs in
-- #eval prime_product 20

/-
info: 0
-/
-- #guard_msgs in
-- #eval prime_product 11

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible