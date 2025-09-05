This kata is inspired on the problem #50 of the Project Euler. 

The prime ``` 41```  is the result of the sum of many consecutive primes.

In fact, ``` 2 + 3 + 5 + 7 + 11 + 13 = 41 , (6 addens)   ``` 

Furthermore, the prime ``` 41```  is the prime below ``` 100 (val_max)```  that has the longest chain of consecutive prime addens.

The prime with longest chain of addens for ```val_max = 500``` is ```499``` with ```17``` addens. 

In fact:
```3+5+7+11+13+17+19+23+29+31+37+41+43+47+53+59+61= 499```

Find the function ```prime_maxlength_chain()```(primeMaxlengthChain() javascript), that receives an argument ```val_max```, the upper limit, all the found primes should be less than ```val_max``` and outputs this found prime.

Let's see some cases:
```python
prime_maxlength_chain(100) == [41]
prime_maxlength_chain(500) == [499]
```
If we have more than one prime with these features, the function should output an array with the found primes sorted.
```python
prime_maxlength_chain(499) == [379, 491]
```
Random Tests for `val_max` (`valMax`)
```
100 ≤ val_max ≤ 500.000
```
Enjoy it!

def isPrime (n : Nat) : Bool := sorry

def primeMaxLengthChain (n : Nat) : List Nat := sorry

def isSorted (l : List Nat) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: y :: rest => x ≤ y && isSorted (y :: rest)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
