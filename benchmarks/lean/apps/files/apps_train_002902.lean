/-
A [sequence or a series](http://world.mathigon.org/Sequences), in mathematics, is a string of objects, like numbers, that follow a particular pattern. The individual elements in a sequence are called terms. A simple example is `3, 6, 9, 12, 15, 18, 21, ...`, where the pattern is: _"add 3 to the previous term"_.

In this kata, we will be using a more complicated sequence:   `0, 1, 3, 6, 10, 15, 21, 28, ...`
This sequence is generated with the pattern: _"the nth term is the sum of numbers from 0 to n, inclusive"_.

```
[ 0,  1,    3,      6,   ...]
  0  0+1  0+1+2  0+1+2+3
```

## Your Task

Complete the function that takes an integer `n` and returns a list/array of length `abs(n) + 1` of the arithmetic series explained above. When`n < 0` return the sequence with negative terms.

## Examples 

```
 5  -->  [0,  1,  3,  6,  10,  15]
-5  -->  [0, -1, -3, -6, -10, -15]
 7  -->  [0,  1,  3,  6,  10,  15,  21,  28]
```
-/

-- <vc-helpers>
-- </vc-helpers>

def sum_of_n (n : Int) : List Int := sorry

theorem sum_of_n_length (n : Int) : (sum_of_n n).length = Int.natAbs n + 1 := sorry

theorem sum_of_n_first_element (n : Int) : 
  (sum_of_n n).get! 0 = 0 := sorry

theorem sum_of_n_consecutive_diffs (n : Int) (i : Nat) 
  (h : i + 1 < (sum_of_n n).length) :
  (sum_of_n n).get! (i + 1) - (sum_of_n n).get! i = 
    if n < 0 
    then (-1 : Int) * (i + 1) 
    else i + 1 := sorry

theorem sum_of_n_signs (n : Int) (i : Nat) 
  (h1 : n ≠ 0)
  (h2 : i > 0) 
  (h3 : i < (sum_of_n n).length) :
  if n < 0 
  then (sum_of_n n).get! i ≤ 0
  else (sum_of_n n).get! i ≥ 0 := sorry

theorem sum_of_n_zero : 
  sum_of_n 0 = [0] := sorry

/-
info: [0, 1, 3, 6]
-/
-- #guard_msgs in
-- #eval sum_of_n 3

/-
info: [0, -1, -3, -6, -10]
-/
-- #guard_msgs in
-- #eval sum_of_n -4

/-
info: [0]
-/
-- #guard_msgs in
-- #eval sum_of_n 0

-- Apps difficulty: introductory
-- Assurance level: unguarded