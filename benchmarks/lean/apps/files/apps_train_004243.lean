/-
Given a number, write a function to output its reverse digits.  (e.g. given 123 the answer is 321)

Numbers should preserve their sign; i.e. a negative number should still be negative when reversed.

### Examples
```
 123 ->  321
-456 -> -654
1000 ->    1
```
-/

-- <vc-helpers>
-- </vc-helpers>

def reverse_number (n : Int) : Int := 
  sorry

theorem sign_preserved (x : Int) : 
  x ≥ 0 → reverse_number x ≥ 0 ∧ 
  x < 0 → reverse_number x < 0 := 
  sorry

theorem trailing_zeros_removed (x n : Nat) :
  x > 0 → 
  n ≥ 0 →
  n ≤ 5 →
  reverse_number (x * 10^n) = 
    reverse_number x :=
  sorry

/-
info: 321
-/
-- #guard_msgs in
-- #eval reverse_number 123

/-
info: -654
-/
-- #guard_msgs in
-- #eval reverse_number -456

/-
info: 1
-/
-- #guard_msgs in
-- #eval reverse_number 1000

-- Apps difficulty: introductory
-- Assurance level: unguarded