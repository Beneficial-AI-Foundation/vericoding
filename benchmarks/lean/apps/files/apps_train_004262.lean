/-
The hamming distance of two equal-length strings is the number of positions, in which the two string differ. In other words, the number of character substitutions required to transform one string into the other. 

For this first Kata, you will write a function ```hamming_distance(a, b)``` with two equal-length strings containing only 0s and 1s as parameters. There is no need to test the parameters for validity (but you can, if you want).The function's output should be the hamming distance of the two strings as an integer.

Example:

```python
hamming_distance('100101', '101001') == 2
hamming_distance('1010', '0101') == 4
```
-/

-- <vc-helpers>
-- </vc-helpers>

def hamming_distance (a b : String) : Nat :=
  sorry

theorem hamming_distance_nonnegative (a b : String) :
  hamming_distance a b ≥ 0 := 
  sorry

theorem hamming_distance_bounded (a b : String) :
  hamming_distance a b ≤ a.length :=
  sorry

theorem hamming_distance_symmetric (a b : String) :
  hamming_distance a b = hamming_distance b a :=
  sorry

theorem hamming_distance_identity (a : String) :
  hamming_distance a a = 0 :=
  sorry

theorem hamming_distance_counts_differences (a b : String) (h : a.length = b.length) :
  hamming_distance a b = ((String.toList a).zip (String.toList b)).countP (fun (x, y) => x ≠ y) :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval hamming_distance "100101" "101001"

/-
info: 4
-/
-- #guard_msgs in
-- #eval hamming_distance "1010" "0101"

/-
info: 9
-/
-- #guard_msgs in
-- #eval hamming_distance "100101011011010010010" "101100010110010110101"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible