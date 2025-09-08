/-
Every natural number, ```n```, may have a prime factorization like:

We define the arithmetic derivative of ```n```, ```n'``` the value of the expression:

Let's do the calculation for ```n = 231525```.
```
231525 = 3³5²7³ 
n' = (3*3²)*5²7³ + 3³*(2*5)*7³ + 3³*5²*(3*7²) = 231525 + 92610 + 99225 = 423360
```
We may make a chain of arithmetic derivatives, starting from a number we apply to the result the transformation and so on until we get the result ```1```.
```
n ---> n'  ---> (n')' ---> ((n')')' ---> ..... ---> ((...(n')...)')'
```
Let's do it starting with our number, ```n = 231525``` and making a chain of 5 terms:
```
231525 ---> 423360 ---> 1899072 ---> 7879680 ---> 51895296
```
We need a function ```chain_arith_deriv()``` that receives two arguments: ```start``` and ```k```, amount of terms of the chain.

The function should output the chain in an array format:
```
chain_arith_deriv(start, k) ---> [start, term1, term2, .....term(k-1)] # a total of k-terms
```
For the case presented above:
```python
chain_arith_deriv(231525, 5) == [231525, 423360, 1899072, 7879680, 51895296]
```
The function has to reject prime numbers giving an alerting message
```python
chain_arith_deriv(997, 5) == "997 is a prime number"
```
Features of the tests:
```
Number of Random Tests: 50
1000 ≤ start ≤ 99000000
3 ≤ k ≤ 15
```
Enjoy it and do your best!
-/

-- <vc-helpers>
-- </vc-helpers>

def isPrime (n : Nat) : Bool := sorry

def chain_arith_deriv (n : Nat) (k : Nat) : String ⊕ List Nat := sorry

theorem chain_length {n k : Nat} (h1 : n ≥ 2) (h2 : k ≥ 1) (h3 : k ≤ 10) :
  let result := chain_arith_deriv n k
  match result with
  | Sum.inl s => ∃ p, isPrime p ∧ s = s!"{p} is a prime number" 
  | Sum.inr l => l.length = k ∧ l.head? = some n
  := sorry

theorem small_primes {p k : Nat} 
  (h1 : p ≥ 2) (h2 : p ≤ 100) (h3 : k ≥ 1) (h4 : k ≤ 10)
  (h5 : isPrime p) :
  chain_arith_deriv p k = Sum.inl s!"{p} is a prime number" := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded