/-
Your task it to return ```true``` if the fractional part (rounded to 1 digit) of the result (```a``` / ```b```) exists, more than ```0``` and is multiple of ```n```.
Otherwise return ```false```. (For Python return True or False)

All arguments are positive digital numbers.

Rounding works like toFixed() method. (if more than...5 rounds up)

Find exapmles below: 

```

isMultiple(5, 2, 3) -> false // 2.5 -> 5 is not multiple of 3
isMultiple(5, 3, 4) -> false // 1.7 -> 7 is not multiple of 4
isMultiple(5, 4, 3) -> true // 1.3 -> 3 is multiple of 3
isMultiple(666, 665, 2) -> false // 1.0 -> return false

```
-/

-- <vc-helpers>
-- </vc-helpers>

def isMultiple (a b n : Nat) : Bool := sorry

theorem isMultiple_deterministic {a b n : Nat} (h1 : 0 < a) (h2 : a ≤ 1000) 
    (h3 : 0 < b) (h4 : b ≤ 1000) (h5 : 0 < n) (h6 : n ≤ 9) :
  isMultiple a b n = isMultiple a b n := sorry

theorem isMultiple_exact_division {a b n : Nat} (h1 : 0 < a) (h2 : a ≤ 1000)
    (h3 : 0 < b) (h4 : b ≤ 1000) (h5 : 0 < n) (h6 : n ≤ 9)
    (h7 : a % b = 0) :
  isMultiple a b n = false := sorry

theorem isMultiple_remainder_bounded {a b : Nat} (h1 : 0 < a) (h2 : a ≤ 1000)
    (h3 : 0 < b) (h4 : b ≤ 1000) :
  let remainder := ((a / b) * 10) % 10
  0 ≤ remainder ∧ remainder ≤ 9 := sorry

theorem isMultiple_div_by_one {a n : Nat} (h1 : 0 < a) (h2 : a ≤ 1000)
    (h3 : 0 < n) (h4 : n ≤ 9) :
  isMultiple a 1 n = false := sorry

theorem isMultiple_zero {b n : Nat} (h1 : 0 < b) (h2 : b ≤ 1000) 
    (h3 : 0 < n) (h4 : n ≤ 9) :
  isMultiple 0 b n = false := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval isMultiple 5 2 3

/-
info: False
-/
-- #guard_msgs in
-- #eval isMultiple 5 3 4

/-
info: True
-/
-- #guard_msgs in
-- #eval isMultiple 5 4 3

-- Apps difficulty: introductory
-- Assurance level: unguarded