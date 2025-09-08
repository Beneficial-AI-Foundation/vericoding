/-
Given an array of positive or negative integers 

 I= [i1,..,in]

you have to produce a sorted array P of the form 

[ [p, sum of all ij of I for which p is a prime factor (p positive) of ij] ...]

P will be sorted by increasing order of the prime numbers.
The final result has to be given as a string in Java, C#, C, C++ and as an array of arrays in other languages.

Example:

```python
I = [12, 15] # result = [[2, 12], [3, 27], [5, 15]]
```

[2, 3, 5] is the list of all prime factors of the elements of I, hence the result.

**Notes:**
- It can happen that a sum is 0 if some numbers are negative!

Example: I = [15, 30, -45]
5 divides 15, 30 and (-45) so 5 appears in the result, the sum of the numbers for which 5 is a factor is 0 so we have [5, 0] in the result amongst others. 

- In Fortran - as in any other language - the returned string is not permitted to contain any redundant trailing whitespace: you can use dynamically allocated character strings.
-/

def isPrime (n : Int) : Bool := sorry

def primeFactor (n: Int) : List Int := sorry

-- <vc-helpers>
-- </vc-helpers>

def sumForList (lst : List Int) : List (Int × Int) := sorry

def listSum (lst : List Int) : Int := lst.foldl (· + ·) 0

theorem results_are_prime_factors {lst : List Int} (h : ∀ x, x ∈ lst → x ≠ 0) :
  ∀ pt, pt ∈ sumForList lst →
    isPrime pt.1 = true ∧ 
    ∃ x, x ∈ lst ∧ x % pt.1 = 0 := sorry

theorem sums_are_correct {lst : List Int} (h : ∀ x, x ∈ lst → x ≠ 0) :
  ∀ pt, pt ∈ sumForList lst →
    pt.2 = listSum (lst.filter (fun x => x % pt.1 = 0)) := sorry

theorem factors_ordered {lst : List Int} (h : ∀ x, x ∈ lst → x ≠ 0) :
  List.Pairwise (· ≤ ·) (List.map Prod.fst (sumForList lst)) := sorry

theorem all_prime_factors_included {lst : List Int} (h : ∀ x, x ∈ lst → x ≠ 0) :
  (∀ p, p ∈ List.map Prod.fst (sumForList lst) → 
    (∃ x, x ∈ lst ∧ x % p = 0 ∧ isPrime p = true)) ∧
  (∀ x, x ∈ lst → ∀ p, p ∈ primeFactor x →
    p ∈ List.map Prod.fst (sumForList lst)) := sorry

/-
info: [[2, 12], [3, 27], [5, 15]]
-/
-- #guard_msgs in
-- #eval sum_for_list [12, 15]

/-
info: [[2, 30], [3, 0], [5, 0]]
-/
-- #guard_msgs in
-- #eval sum_for_list [15, 30, -45]

/-
info: [[2, 54], [3, 135], [5, 90], [7, 21]]
-/
-- #guard_msgs in
-- #eval sum_for_list [15, 21, 24, 30, 45]

-- Apps difficulty: interview
-- Assurance level: unguarded