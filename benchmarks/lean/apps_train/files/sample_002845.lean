/-
## Nova polynomial add

This kata is from a series on polynomial handling. ( [#1](http://www.codewars.com/kata/nova-polynomial-1-add-1) [#2](http://www.codewars.com/kata/570eb07e127ad107270005fe) [#3](http://www.codewars.com/kata/5714041e8807940ff3001140 ) [#4](http://www.codewars.com/kata/571a2e2df24bdfd4e20001f5) )

Consider a polynomial in a list where each element in the list element corresponds to a factor. The factor order is the position in the list. The first element is the zero order factor (the constant).

`p = [a0, a1, a2, a3]` signifies the polynomial `a0 + a1x + a2x^2 + a3*x^3`

In this kata add two polynomials:

```python
poly_add ( [1, 2], [1] ) = [2, 2]
```
-/

-- <vc-helpers>
-- </vc-helpers>

def poly_add (p1 p2 : List Int) : List Int := sorry

theorem poly_add_length (p1 p2 : List Int) :
  (poly_add p1 p2).length = max p1.length p2.length := sorry

theorem poly_add_empty_left (p : List Int) :
  poly_add [] p = p := sorry

theorem poly_add_empty_right (p : List Int) :
  poly_add p [] = p := sorry

theorem poly_add_comm (p1 p2 : List Int) :
  poly_add p1 p2 = poly_add p2 p1 := sorry

theorem poly_add_coeff (p1 p2 : List Int) (i : Nat) (h1 : i < p1.length) (h2 : i < p2.length) 
  (h3 : i < (poly_add p1 p2).length) :
  (poly_add p1 p2)[i] = p1[i] + p2[i] := sorry

theorem poly_add_zeros (p : List Int) :
  poly_add p (List.replicate p.length 0) = p := sorry

/-
info: [2]
-/
-- #guard_msgs in
-- #eval poly_add [1] [1]

/-
info: [2, 2]
-/
-- #guard_msgs in
-- #eval poly_add [1, 2] [1]

/-
info: [5, 5, 5, 5]
-/
-- #guard_msgs in
-- #eval poly_add [1, 2, 3, 4] [4, 3, 2, 1]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible