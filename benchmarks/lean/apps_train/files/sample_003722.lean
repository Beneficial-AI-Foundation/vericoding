/-
# Task
 The `hamming distance` between a pair of numbers is the number of binary bits that differ in their binary notation. 

# Example

 For `a = 25, b= 87`, the result should be `4`
```
25: 00011001
87: 01010111
```
The `hamming distance` between these two would be 4 ( the `2nd, 5th, 6th, 7th` bit ).

# Input/Output

 - `[input]` integer `a`

  First Number. `1 <= a <= 2^20`

 - `[input]` integer `b`

  Second Number. `1 <= b <= 2^20`

 - `[output]` an integer

  Hamming Distance
-/

-- <vc-helpers>
-- </vc-helpers>

def hamming_distance : Int → Int → Nat := 
  sorry

/- Hamming distance is symmetric -/

theorem hamming_distance_symmetric (a b : Int) : 
  hamming_distance a b = hamming_distance b a := by
  sorry

/- Hamming distance between a number and itself is zero -/

theorem hamming_distance_self_zero (a : Int) : 
  hamming_distance a a = 0 := by
  sorry

/- Hamming distance satisfies the triangle inequality -/

theorem hamming_distance_triangle_inequality (a b c : Int) :
  hamming_distance a c ≤ hamming_distance a b + hamming_distance b c := by
  sorry

/- Hamming distance is always nonnegative -/

theorem hamming_distance_nonnegative (a b : Int) :
  hamming_distance a b ≥ 0 := by
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval hamming_distance 25 87

/-
info: 4
-/
-- #guard_msgs in
-- #eval hamming_distance 256 302

/-
info: 4
-/
-- #guard_msgs in
-- #eval hamming_distance 543 634

-- Apps difficulty: introductory
-- Assurance level: guarded