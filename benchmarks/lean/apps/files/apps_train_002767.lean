/-
This kata is an extension of "Combinations in a Set Using Boxes":https://www.codewars.com/kata/5b5f7f7607a266914200007c

The goal for this kata is to get all the possible combinations (or distributions) (with no empty boxes) of a certain number of balls, but now, **with different amount of boxes.** In the previous kata, the number of boxes was always the same

Just to figure the goal for this kata, we can see in the picture below the combinations for four balls using the diagram of Hasse:

Points that are isolated represent balls that are unique in a box.
k points that are bonded in an area respresent a subset that is content in a box.

The unique square at the bottom of the diagram, means that there is only one possible combination for four balls in four boxes.

The above next line with 6 squares, means that we have 6 possible distributions of the four balls in 3 boxes. These six distributions have something in common, all of them have one box with 2 balls.

Going up one line more, we find the 7 possible distributions of the four balls in 2 boxes. As it is shown, we will have 7 distributions with: three balls in a box and only one ball in the another box, or two balls in each box.

Finally, we find again at the top, an unique square, that represents, the only possible distribution, having one box, the four balls together in the only available box.

So, for a set of 4 labeled balls, we have a total of 15 possible distributions (as always with no empty boxes) and with a maximum of 7 possible distributions for the case of two boxes.

Prepare a code that for a given number of balls (an integer), may output an array with required data in the following order:
```
[total_amount_distributions, maximum_amount_distributions_case_k_boxes, k_boxes]
```
Just see how it would be for the example given above:
```
combs_non_empty_boxesII(4) == [15, 7, 2] # A total of 15 combinations            
                                         #The case with maximum distributions is 7 using 2 boxes.

```
Features of the random tests:
```
1 < n <= 1800 (python)
1 < n <= 1200 (ruby)
```
You may see the example tests for more cases.
Enjoy it!
Ruby version will be published soon.
-/

-- <vc-helpers>
-- </vc-helpers>

def combs_non_empty_boxesII (n : Nat) : List Nat := sorry

-- Output has length 3 and contains only natural numbers

theorem output_structure (n : Nat) (h : n > 0) (h2 : n ≤ 20) : 
  let result := combs_non_empty_boxesII n
  result.length = 3 ∧ (∀ x ∈ result, x ≥ 0) := sorry

-- First element is positive

theorem first_value_positive (n : Nat) (h : n > 0) (h2 : n ≤ 20) :
  (combs_non_empty_boxesII n).get! 0 > 0 := sorry

-- Second element is less than or equal to first element

theorem second_value_less_than_first (n : Nat) (h : n > 0) (h2 : n ≤ 20) :
  (combs_non_empty_boxesII n).get! 1 ≤ (combs_non_empty_boxesII n).get! 0 := sorry

-- Third element is in valid range

theorem index_in_valid_range (n : Nat) (h : n > 0) (h2 : n ≤ 20) :
  let result := (combs_non_empty_boxesII n).get! 2
  1 ≤ result ∧ result ≤ n := sorry

-- Minimal case when n = 1

theorem minimal_case :
  combs_non_empty_boxesII 1 = [1, 1, 1] := sorry

-- Monotonic first value

theorem monotonic_first_value (n : Nat) (h : n > 1) (h2 : n ≤ 20) :
  (combs_non_empty_boxesII (n-1)).get! 0 < (combs_non_empty_boxesII n).get! 0 := sorry

/-
info: [15, 7, 2]
-/
-- #guard_msgs in
-- #eval combs_non_empty_boxesII 4

/-
info: [5, 3, 2]
-/
-- #guard_msgs in
-- #eval combs_non_empty_boxesII 3

/-
info: [2, 1, 2]
-/
-- #guard_msgs in
-- #eval combs_non_empty_boxesII 2

-- Apps difficulty: introductory
-- Assurance level: unguarded