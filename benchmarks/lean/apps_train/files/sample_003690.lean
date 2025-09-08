/-
In this Kata, you will be given an integer array and your task is to return the sum of elements occupying prime-numbered indices. 

~~~if-not:fortran
The first element of the array is at index `0`.
~~~

~~~if:fortran
The first element of an array is at index `1`.
~~~

Good luck! 

If you like this Kata, try:

[Dominant primes](https://www.codewars.com/kata/59ce11ea9f0cbc8a390000ed). It takes this idea a step further.

[Consonant value](https://www.codewars.com/kata/59c633e7dcc4053512000073)
-/

def is_prime (n : Nat) : Bool :=
  sorry

def total (arr : List Int) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def sqrt (n : Nat) : Nat :=
  sorry

theorem total_empty_property (arr : List Int) :
  arr = [] → total arr = 0 :=
sorry

theorem total_properties (arr : List Int) :
  total arr = (List.enum arr).foldl (fun acc (i, x) => if is_prime i then acc + x else acc) 0 :=
sorry

theorem total_sign (arr : List Int) :
  total arr ≥ 0 ∨ ∃ x ∈ arr, x < 0 :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval total []

/-
info: 7
-/
-- #guard_msgs in
-- #eval total [1, 2, 3, 4]

/-
info: 21
-/
-- #guard_msgs in
-- #eval total [1, 2, 3, 4, 5, 6, 7, 8]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible