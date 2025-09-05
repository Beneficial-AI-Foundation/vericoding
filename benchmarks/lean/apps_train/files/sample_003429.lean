Define a "prime prime" number to be a rational number written as one prime number over another prime number: `primeA / primeB` (e.g. `7/31`)

Given a whole number `N`, generate the number of "prime prime" rational numbers less than 1, using only prime numbers between `0` and `N` (non inclusive).

Return the count of these "prime primes", and the integer part  of their sum.

## Example

```python
N = 6

# The "prime primes" less than 1 are:
2/3, 2/5, 3/5               # count: 3

2/3 + 2/5 + 3/5 = 1.6667    # integer part: 1

Thus, the function should return 3 and 1.
```

def sieve (n : Nat) : List Nat := sorry

def prime_primes (n : Nat) : Nat × Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible