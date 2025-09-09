/-
*** Nova polynomial subtract*** 

This kata is from a series on polynomial handling. ( [#1](http://www.codewars.com/kata/nova-polynomial-1-add-1)   [#2](http://www.codewars.com/kata/570eb07e127ad107270005fe)  [#3](http://www.codewars.com/kata/5714041e8807940ff3001140 )   [#4](http://www.codewars.com/kata/571a2e2df24bdfd4e20001f5))

Consider a polynomial in a list where each element in the list element corresponds to the factors. The factor order is the position in the list. The first element is the zero order factor (the constant).

p = [a0, a1, a2, a3] signifies the polynomial a0 + a1x + a2x^2 + a3*x^3

In this kata subtract two polynomials:

```python 
poly_subtract([1, 2], [1] ) = [0, 2]
poly_subtract([2, 4], [4, 5] ) = [-2, -1]
```
The first and second katas of this series are preloaded in the code and can be used: 

 * [poly_add](http://www.codewars.com/kata/nova-polynomial-1-add-1) 
 * [poly_multiply](http://www.codewars.com/kata/570eb07e127ad107270005fe).
-/

-- <vc-helpers>
-- </vc-helpers>

def poly_subtract : List Int → List Int → List Int
  | p1, p2 => sorry

theorem poly_subtract_length (p1 p2 : List Int) :
  p1.length > 0 ∨ p2.length > 0 →
  (poly_subtract p1 p2).length ≤ max p1.length p2.length := sorry

theorem poly_subtract_self (p : List Int) :
  ∀ x ∈ poly_subtract p p, x = 0 := sorry

theorem poly_subtract_empty (p : List Int) :
  poly_subtract p [] = p := sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval poly_subtract [] []

/-
info: [1, 2, 3, 4, 5, 6]
-/
-- #guard_msgs in
-- #eval poly_subtract [1, 2, 3, 4, 5, 6] []

/-
info: [-1, -2, -3, -4, -5, -6]
-/
-- #guard_msgs in
-- #eval poly_subtract [] [1, 2, 3, 4, 5, 6]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible