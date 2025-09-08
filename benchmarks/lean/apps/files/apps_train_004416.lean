/-
# Task
A masked number is a string that consists of digits and one asterisk (`*`) that should be replaced by exactly one digit. Given a masked number `s`, find all the possible options to replace the asterisk with a digit to produce an integer divisible by 6.

# Input/Output

`[input]` string `s`

A masked number.

`1 ≤ inputString.length ≤ 10000.`

`[output]` a string array

Sorted array of strings representing all non-negative integers that correspond to the given mask and are divisible by 6.

# Example

For `s = "1*0"`, the output should be `["120", "150", "180"].`

For `s = "*1"`, the output should be `[].`

For `s = "1234567890123456789012345678*0"`, 

the output should be 
```
[
"123456789012345678901234567800",
"123456789012345678901234567830",
"123456789012345678901234567860",
"123456789012345678901234567890"]```
As you can see, the masked number may be very large ;-)
-/

-- <vc-helpers>
-- </vc-helpers>

def is_divisible_by_6 (s: String) : List String := sorry

theorem is_divisible_by_6_length_constraints {s : String} :
  s.length = 0 ∨ s.length > 10000 → is_divisible_by_6 s = [] := sorry

theorem is_divisible_by_6_all_divisible {s : String} (h : s.length > 0) (h' : s.length ≤ 10000) :
  ∀ x ∈ is_divisible_by_6 s, (String.toNat! x) % 6 = 0 := sorry 

theorem is_divisible_by_6_sorted {s : String} (h : s.length > 0) (h' : s.length ≤ 10000) :
  ∀ i j, i < j → i < (is_divisible_by_6 s).length → j < (is_divisible_by_6 s).length → 
    (is_divisible_by_6 s)[i]! < (is_divisible_by_6 s)[j]! := sorry

theorem is_divisible_by_6_no_leading_zeros {s : String} (h : s.length > 0) (h' : s.length ≤ 10000) :
  ∀ x ∈ is_divisible_by_6 s, ¬String.startsWith x "0" := sorry

/-
info: ['120', '150', '180']
-/
-- #guard_msgs in
-- #eval is_divisible_by_6 "1*0"

/-
info: []
-/
-- #guard_msgs in
-- #eval is_divisible_by_6 "*1"

/-
info: ['36', '66', '96']
-/
-- #guard_msgs in
-- #eval is_divisible_by_6 "*6"

-- Apps difficulty: introductory
-- Assurance level: unguarded