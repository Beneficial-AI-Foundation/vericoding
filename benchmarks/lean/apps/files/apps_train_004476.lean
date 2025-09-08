/-
We need a function ```prime_bef_aft()``` that gives the largest prime below a certain given value ```n```, 

```befPrime or bef_prime``` (depending on the language), 

and the smallest prime larger than this value, 

```aftPrime/aft_prime``` (depending on the language).

The result should be output in a list like the following:

```python
prime_bef_aft(n) == [befPrime, aftPrime]
```

If n is a prime number it will give two primes, n will not be included in the result.

Let's see some cases:
```python
prime_bef_aft(100) == [97, 101]

prime_bef_aft(97) == [89, 101]

prime_bef_aft(101) == [97, 103]
```
Range for the random tests: 
```1000 <= n <= 200000```

(The extreme and special case n = 2 will not be considered for the tests. Thanks Blind4Basics)

Happy coding!!
-/

-- <vc-helpers>
-- </vc-helpers>

def prime (n : Nat) : Bool := sorry

def prime_bef_aft (n : Nat) : Nat × Nat := sorry

theorem prime_bef_aft_bound {n : Nat} (h : n ≥ 4) (h2 : n ≤ 1000) :
  let (p1, p2) := prime_bef_aft n
  p1 < n ∧ n < p2 := sorry

theorem prime_bef_aft_primes {n : Nat} (h : n ≥ 4) (h2 : n ≤ 1000) :
  let (p1, p2) := prime_bef_aft n
  prime p1 = true ∧ prime p2 = true := sorry

theorem prime_bef_aft_nat {n : Nat} (h : n ≥ 4) (h2 : n ≤ 1000) :
  let (p1, p2) := prime_bef_aft n
  p1 ≥ 0 ∧ p2 ≥ 0 := sorry

theorem prime_divisibility {n : Nat} (h : n ≥ 2) (h2 : n ≤ 100) :
  prime n = true ↔ ∀ i : Nat, 2 ≤ i → i < n → n % i ≠ 0 := sorry

theorem composite_divisibility {n : Nat} (h : n ≥ 2) (h2 : n ≤ 100) :
  prime n = false → ∃ i : Nat, 2 ≤ i ∧ i < n ∧ n % i = 0 := sorry

/-
info: [97, 101]
-/
-- #guard_msgs in
-- #eval prime_bef_aft 100

/-
info: [89, 101]
-/
-- #guard_msgs in
-- #eval prime_bef_aft 97

/-
info: [97, 103]
-/
-- #guard_msgs in
-- #eval prime_bef_aft 101

-- Apps difficulty: introductory
-- Assurance level: guarded