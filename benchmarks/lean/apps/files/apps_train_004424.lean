/-
Calculus class...is awesome! But you are a programmer with no time for mindless repetition. Your teacher spent a whole day covering differentiation of polynomials, and by the time the bell rang, you had already conjured up a program to automate the process.

You realize that a polynomial of degree n

anx^(n) + an-1x^(n-1) + ... + a0

can be represented as an array of coefficients

[an, an-1, ...,  a0]

For example, we would represent

5x^(2) + 2x + 1 as [5,2,1]

3x^(2) + 1 as [3,0,1]

x^(4) as [1,0,0,0,0]

x as [1, 0]

1 as [1]

Your function will take a coefficient array as an argument and return a **new array** representing the coefficients of the derivative.

```python
poly1 = [1, 1] # x + 1
diff(poly1) == [1] # 1

poly2 = [1, 1, 1] # x^2 + x + 1
diff(poly2) == [2, 1] # 2x + 1
diff(diff(poly2)) == [2] # 2

poly3 = [2, 1, 0, 0] # 2x^3 + x^2
diff(poly3) == [6, 2, 0] # 6x^2 + 2x
```
Note: your function will always return a new array which has one less element than the argument (unless the argument is [], in which case [] is returned).
-/

-- <vc-helpers>
-- </vc-helpers>

def diff (p : List Int) : List Int := sorry

theorem diff_length (p : List Int) :
  (diff p).length = max 0 (p.length - 1) := sorry

theorem diff_constant (p : List Int) :
  p.length = 1 → diff p = [] := sorry

theorem diff_linear (p : List Int) :
  p.length = 2 → diff p = [p.get! 0] := sorry

theorem double_diff_quadratic (p : List Int) :
  p.length = 3 → diff (diff p) = [2 * p.get! 0] := sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval diff []

/-
info: [1]
-/
-- #guard_msgs in
-- #eval diff [1, 1]

/-
info: [6, 2, 0]
-/
-- #guard_msgs in
-- #eval diff [2, 1, 0, 0]

-- Apps difficulty: introductory
-- Assurance level: guarded