/-
There is a room with n lights which are turned on initially and 4 buttons on the wall. After performing exactly m unknown operations towards buttons, you need to return how many different kinds of status of the n lights could be.

Suppose n lights are labeled as number [1, 2, 3 ..., n], function of these 4 buttons are given below:

Flip all the lights.
Flip lights with even numbers.
Flip lights with odd numbers.
Flip lights with (3k + 1) numbers, k = 0, 1, 2, ...

Example 1:

Input: n = 1, m = 1.
Output: 2
Explanation: Status can be: [on], [off]

Example 2:

Input: n = 2, m = 1.
Output: 3
Explanation: Status can be: [on, off], [off, on], [off, off]

Example 3:

Input: n = 3, m = 1.
Output: 4
Explanation: Status can be: [off, on, off], [on, off, on], [off, off, off], [off, on, on].

Note:
n and m both fit in range [0, 1000].
-/

-- <vc-helpers>
-- </vc-helpers>

def flipLights (n : Nat) (m : Nat) : Nat :=
  sorry

-- Output should be between 1 and 4 positions

theorem output_range (n m : Nat) : 
  n > 0 → 
  1 ≤ flipLights n m ∧ 
  flipLights n m ≤ min 16 (2 ^ (min n 4)) :=
sorry

-- Zero operations should result in one possible state

theorem zero_operations (n : Nat) :
  n > 0 →
  flipLights n 0 = 1 :=
sorry

-- Result should stabilize for large m

theorem operation_stabilization (n : Nat) :
  n > 0 →
  flipLights n 1000 = flipLights n 1001 :=
sorry

-- More lights should never decrease possible states

theorem monotonic_n (n m : Nat) :
  n > 1 →
  flipLights (n-1) m ≤ flipLights n m :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval flipLights 1 1

/-
info: 3
-/
-- #guard_msgs in
-- #eval flipLights 2 1

/-
info: 4
-/
-- #guard_msgs in
-- #eval flipLights 3 1

-- Apps difficulty: interview
-- Assurance level: unguarded