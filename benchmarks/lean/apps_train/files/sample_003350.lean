A [Mersenne prime](https://en.wikipedia.org/wiki/Mersenne_prime) is a prime number that can be represented as:
Mn = 2^(n) - 1. Therefore, every Mersenne prime is one less than a power of two. 

Write a function that will return whether the given integer `n` will produce a Mersenne prime or not.

The tests will check random integers up to 2000.

def valid_mersenne (n : Int) : Bool := sorry

theorem valid_mersenne_returns_bool (n : Int) :
  valid_mersenne n = true ∨ valid_mersenne n = false := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded