/-
Your task is to create function```isDivideBy``` (or ```is_divide_by```) to check if an integer number is divisible by each out of two arguments.

A few cases:

```

(-12, 2, -6)  ->  true
(-12, 2, -5)  ->  false

(45, 1, 6)    ->  false
(45, 5, 15)   ->  true

(4, 1, 4)     ->  true
(15, -5, 3)   ->  true

```
-/

-- <vc-helpers>
-- </vc-helpers>

def is_divide_by (n a b : Int) : Bool := sorry

theorem is_divide_by_correct (n a b : Int) (ha : a ≠ 0) (hb : b ≠ 0) : 
  is_divide_by n a b = true ↔ n % a = 0 ∧ n % b = 0 := sorry

theorem divide_by_one (n : Int) :
  is_divide_by n 1 1 = true := sorry

theorem divide_by_self (n a : Int) (h : a ≠ 0) :
  is_divide_by a a a = true := sorry

theorem divide_by_zero_error (n : Int) :
  is_divide_by n 0 1 = false ∧ is_divide_by n 1 0 = false := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_divide_by -12 2 -6

/-
info: False
-/
-- #guard_msgs in
-- #eval is_divide_by 45 1 6

/-
info: True
-/
-- #guard_msgs in
-- #eval is_divide_by 15 -5 3

-- Apps difficulty: introductory
-- Assurance level: unguarded