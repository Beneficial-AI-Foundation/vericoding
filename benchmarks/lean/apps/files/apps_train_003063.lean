/-
Given two integers `a` and `b`, which can be positive or negative, find the sum of all the numbers between including them too and return it. If the two numbers are equal return `a` or `b`.

**Note:** `a` and `b` are not ordered!

## Examples

```python
get_sum(1, 0) == 1   // 1 + 0 = 1
get_sum(1, 2) == 3   // 1 + 2 = 3
get_sum(0, 1) == 1   // 0 + 1 = 1
get_sum(1, 1) == 1   // 1 Since both are same
get_sum(-1, 0) == -1 // -1 + 0 = -1
get_sum(-1, 2) == 2  // -1 + 0 + 1 + 2 = 2
```
```C
get_sum(1, 0) == 1   // 1 + 0 = 1
get_sum(1, 2) == 3   // 1 + 2 = 3
get_sum(0, 1) == 1   // 0 + 1 = 1
get_sum(1, 1) == 1   // 1 Since both are same
get_sum(-1, 0) == -1 // -1 + 0 = -1
get_sum(-1, 2) == 2  // -1 + 0 + 1 + 2 = 2
```
-/

def abs (n : Int) : Int :=
  if n ≥ 0 then n else -n

-- <vc-helpers>
-- </vc-helpers>

def get_sum (a b : Int) : Int := sorry

theorem get_sum_commutative (a b : Int) : 
  get_sum a b = get_sum b a := sorry

theorem get_sum_same_number (n : Int) :
  get_sum n n = n := sorry

theorem get_sum_consecutive (a b : Int) :
  a ≠ b → get_sum a b = ((a + b) / 2) * (abs (b - a) + 1) := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval get_sum 1 3

/-
info: 2
-/
-- #guard_msgs in
-- #eval get_sum -1 2

/-
info: 5
-/
-- #guard_msgs in
-- #eval get_sum 5 5

-- Apps difficulty: introductory
-- Assurance level: unguarded