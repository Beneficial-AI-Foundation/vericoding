Given a positive number n > 1 find the prime factor decomposition of n.
The result will be a string with the following form :
```
 "(p1**n1)(p2**n2)...(pk**nk)"
```
where ```a ** b``` means ```a``` to the power of ```b```

with the p(i) in increasing order and n(i) empty if
n(i) is 1.
```
Example: n = 86240 should return "(2**5)(5)(7**2)(11)"
```

def is_prime (n : Nat) : Bool := sorry

def get_factors (n : Nat) : List Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
