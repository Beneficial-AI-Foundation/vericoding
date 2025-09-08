/-
Get the next prime number!

You will get a number`n` (>= 0) and your task is to find the next prime number. 

Make sure to optimize your code: there will numbers tested up to about `10^12`.

## Examples

```
5   =>  7
12  =>  13
```
-/

-- <vc-helpers>
-- </vc-helpers>

def is_prime : Int → Bool := sorry
def next_prime : Int → Int := sorry

theorem next_prime_larger (n : Int) :
  next_prime n > n := sorry

theorem next_prime_is_prime (n : Int) : 
  is_prime (next_prime n) = true := sorry

theorem no_primes_between (n : Int) :
  ∀ x, n < x → x < next_prime n → is_prime x = false := sorry

theorem prime_returns_self {n : Int} (h : n ≥ 2) (h2 : is_prime n = true) : 
  next_prime (n - 1) = n := sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval next_prime 5

/-
info: 13
-/
-- #guard_msgs in
-- #eval next_prime 12

/-
info: 2
-/
-- #guard_msgs in
-- #eval next_prime 0

-- Apps difficulty: introductory
-- Assurance level: guarded