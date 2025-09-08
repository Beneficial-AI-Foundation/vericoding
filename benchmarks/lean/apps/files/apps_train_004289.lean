/-
A number is simply made up of digits.  
The number 1256 is made up of the digits 1, 2, 5, and 6.  
For 1256 there are 24 distinct permutations of the digits:  
1256, 1265, 1625, 1652, 1562, 1526, 2156, 2165, 2615, 2651, 2561, 2516,   
5126, 5162, 5216, 5261, 5621, 5612, 6125, 6152, 6251, 6215, 6521, 6512.

Your goal is to write a program that takes a number, n, and returns the average value of all distinct permutations of the digits in n.  Your answer should be rounded to the nearest integer. For the example above the return value would be 3889. * 

  n will never be negative

A few examples:
```python
permutation_average(2)
return 2

permutation_average(25)
>>> 25 + 52 = 77
>>> 77 / 2 = 38.5
return 39 *

permutation_average(20)
>>> 20 + 02 = 22
>>> 22 / 2 = 11
return 11

permutation_average(737)
>>> 737 + 377 + 773 = 1887
>>> 1887 / 3 = 629
return 629

```

Note: Your program should be able to handle numbers up to 6 digits long
~~~if:python
\* Python version 3 and above uses Banker Rounding so the expected values for those tests would be 3888 and 38 respectively
~~~
~~~if-not:python
\* ignore these marks, they're for Python only
~~~
-/

def permutation_average (n : Int) : Int := 
  sorry

-- <vc-helpers>
-- </vc-helpers>

def permutation_average_str (s : String) : Int := 
  sorry

theorem permutation_average_returns_integer (n : Int) 
  (h : 0 ≤ n ∧ n ≤ 999) : 
  ∃ i : Int, permutation_average n = i := by
  sorry

theorem string_int_equivalent (n : Int) 
  (h : 0 ≤ n ∧ n ≤ 999) :
  permutation_average n = permutation_average_str (toString n) := by
  sorry

theorem leading_zeros_valid (n : Int)
  (h : 0 ≤ n ∧ n ≤ 99) :
  ∃ i : Int, permutation_average_str ("0" ++ toString n) = i := by
  sorry 

theorem result_within_bounds (n : Int)
  (h : 10 ≤ n ∧ n ≤ 999) :
  permutation_average n ≥ 0 ∧ permutation_average n ≤ n := by
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval permutation_average 2

/-
info: 38
-/
-- #guard_msgs in
-- #eval permutation_average 25

/-
info: 629
-/
-- #guard_msgs in
-- #eval permutation_average 737

-- Apps difficulty: introductory
-- Assurance level: unguarded