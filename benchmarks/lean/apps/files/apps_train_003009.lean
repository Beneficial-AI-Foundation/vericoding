/-
# Task
 Suppose there are `n` people standing in a circle and they are numbered 1 through n in order. 

 Person 1 starts off with a sword and kills person 2. He then passes the sword to the next person still standing, in this case person 3. Person 3 then uses the sword to kill person 4, and passes it to person 5. This pattern continues around and around the circle until just one person remains.

 What is the number of this person? 

# Example: 

 For `n = 5`, the result should be `3`.
```
1 kills 2, passes to 3.
3 kills 4, passes to 5.
5 kills 1, passes to 3.
3 kills 5 and wins.```

# Input/Output

 - `[input]` integer `n`

  The number of people. 1 through n standing in a circle.

  `1 <= n <= 1e9`

 - `[output]` an integer

  The index of the last person standing.
-/

-- <vc-helpers>
-- </vc-helpers>

def circle_slash (n : Nat) : Nat :=
  sorry

/-
  Main property theorems
-/

theorem circle_slash_range (n : Nat) (h : n > 0) :
  1 ≤ circle_slash n ∧ circle_slash n ≤ n :=
  sorry

theorem circle_slash_odd_unless_power_of_two (n : Nat) (h : n > 0) 
  (h_not_power_2 : ¬∃k, n = 2^k) :
  circle_slash n % 2 = 1 :=
  sorry

theorem circle_slash_power_of_two (k : Nat) :
  circle_slash (2^k) = 1 :=
  sorry

/-
  Pattern theorems
-/

theorem circle_slash_binary_pattern (n : Nat) (h : n > 1) :
  -- For n > 1, removing leading '1' from binary representation and appending '1'
  circle_slash n = (n % (2^(Nat.log2 n))) * 2 + 1 :=
  sorry

theorem circle_slash_one :
  circle_slash 1 = 1 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval circle_slash 5

/-
info: 7
-/
-- #guard_msgs in
-- #eval circle_slash 11

/-
info: 1
-/
-- #guard_msgs in
-- #eval circle_slash 16

-- Apps difficulty: introductory
-- Assurance level: unguarded