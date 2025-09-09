/-
There are N children standing in a line. Each child is assigned a rating value.

You are giving candies to these children subjected to the following requirements:

       Each child must have at least one candy.
       Children with a higher rating get more candies than their neighbors.

What is the minimum candies you must give?

Example 1:

Input: [1,0,2]
Output: 5
Explanation: You can allocate to the first, second and third child with 2, 1, 2 candies respectively.

Example 2:

Input: [1,2,2]
Output: 4
Explanation: You can allocate to the first, second and third child with 1, 2, 1 candies respectively.
             The third child gets 1 candy because it satisfies the above two conditions.
-/

-- <vc-helpers>
-- </vc-helpers>

def candy (ratings : List Nat) : Nat := sorry

theorem candy_empty :
  candy [] = 0 := sorry

theorem candy_single (rating : Nat) :
  candy [rating] = 1 := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval candy [1, 0, 2]

/-
info: 4
-/
-- #guard_msgs in
-- #eval candy [1, 2, 2]

/-
info: 0
-/
-- #guard_msgs in
-- #eval candy []

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible