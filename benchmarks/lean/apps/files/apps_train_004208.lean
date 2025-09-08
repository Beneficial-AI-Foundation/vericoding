/-
# Task

Find the integer from `a` to `b` (included) with the greatest number of divisors. For example:

```
divNum(15, 30)   ==> 24
divNum(1, 2)     ==> 2
divNum(0, 0)     ==> 0
divNum(52, 156)  ==> 120
```

If there are several numbers that have the same (maximum) number of divisors, the smallest among them should be returned. Return the string `"Error"` if `a > b`.
-/

def countDivisors (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def divNum (a b : Nat) : Option Nat := 
  sorry

theorem divNum_invalid_range {a b : Nat} (h : a > b) : 
  divNum a b = none := 
  sorry

theorem divNum_result_in_range {a b : Nat} (h : a ≤ b) (result : Nat) :
  divNum a b = some result → a ≤ result ∧ result ≤ b :=
  sorry  

theorem divNum_max_divisors {a b result : Nat} (h : a ≤ b) :
  divNum a b = some result →
  ∀ x, a ≤ x ∧ x ≤ b → countDivisors x ≤ countDivisors result :=
  sorry

theorem divNum_equal_inputs (x : Nat) :
  divNum x x = some x :=
  sorry

/-
info: 24
-/
-- #guard_msgs in
-- #eval div_num 15 30

/-
info: 2
-/
-- #guard_msgs in
-- #eval div_num 1 2

/-
info: 'Error'
-/
-- #guard_msgs in
-- #eval div_num 159 4

-- Apps difficulty: introductory
-- Assurance level: unguarded