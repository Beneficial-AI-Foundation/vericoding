/-
Given a list of prime factors, ```primesL```, and an integer, ```limit```, try to generate in order, all the numbers less than the value of ```limit```, that have **all and only** the prime factors of ```primesL```

## Example
```python
primesL = [2, 5, 7]
limit = 500
List of Numbers Under 500          Prime Factorization
___________________________________________________________
           70                         [2, 5, 7]
          140                         [2, 2, 5, 7]
          280                         [2, 2, 2, 5, 7]
          350                         [2, 5, 5, 7]
          490                         [2, 5, 7, 7]
```

There are ```5``` of these numbers under ```500``` and the largest one is ```490```.

## Task

For this kata you have to create the function ```count_find_num()```, that accepts two arguments: ```primesL``` and ```limit```, and returns the amount of numbers that fulfill the requirements, and the largest number under `limit`.

The example given above will be:
```python
primesL = [2, 5, 7]
limit = 500
count_find_num(primesL, val) == [5, 490]
```

If no numbers can be generated under `limit` then return an empty list:
```python
primesL = [2, 3, 47]
limit = 200
find_nums(primesL, limit) == []
```

The result should consider the limit as inclusive:
```python
primesL = [2, 3, 47]
limit = 282
find_nums(primesL, limit) == [1, 282]
```

Features of the random tests:
```
number of tests = 200
2 <= length_primesL <= 6 // length of the given prime factors array
5000 <= limit <= 1e17
2 <= prime <= 499  // for every prime in primesL
```

Enjoy!
-/

def List.prod : List Nat → Nat 
  | [] => 1
  | x :: xs => x * List.prod xs

-- <vc-helpers>
-- </vc-helpers>

def count_find_num (primes: List Nat) (limit: Nat) : Option (Nat × Nat) := sorry

theorem count_find_num_basic_props {primes: List Nat} {limit: Nat} :
  match count_find_num primes limit with
  | none => ∀ p ∈ primes, p ≥ 2 → (List.prod primes > limit) 
  | some (count, max_val) => 
      (∀ p ∈ primes, p ≥ 2) →
      List.prod primes ≤ limit ∧ 
      max_val ≤ limit ∧
      count ≥ 1 ∧
      max_val ≥ List.prod primes
  := sorry

theorem count_find_num_divisible {primes: List Nat} {limit: Nat} :
  match count_find_num primes limit with
  | none => True
  | some (count, max_val) =>
      ∀ p ∈ primes, max_val % p = 0
  := sorry

theorem count_find_num_edge_cases_1 :
  count_find_num [2] 1 = none := sorry

theorem count_find_num_edge_cases_2 :
  count_find_num [2] 2 = some (1, 2) := sorry

theorem count_find_num_edge_cases_3 :
  count_find_num [2, 3] 5 = none := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded