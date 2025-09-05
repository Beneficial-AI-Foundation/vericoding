*** Nova polynomial from roots*** 

This kata is from a series on polynomial handling. ( [#1](http://www.codewars.com/kata/nova-polynomial-1-add-1)   [#2](http://www.codewars.com/kata/570eb07e127ad107270005fe)  [#3](http://www.codewars.com/kata/5714041e8807940ff3001140 )   [#4](http://www.codewars.com/kata/571a2e2df24bdfd4e20001f5))

Consider a polynomial in a list where each element in the list element corresponds to the factors. The factor order is the position in the list. The first element is the zero order factor (the constant).

p = [a0, a1, a2, a3] signifies the polynomial a0 + a1x + a2x^2 + a3*x^3

In this kata create the polynomial from a list of roots:

[r0, r1 ,r2, r3 ]

p = (x-r0)(x-r1)(x-r2)(x-r3)

note: no roots should return the identity polynomial.

```python 
poly_from_roots([4]) = [-4, 1]
poly_from_roots([0, 0, 0, 0] ) = [0, 0, 0, 0, 1]
poly_from_roots([]) = [1]
```
The first katas of this series is preloaded in the code and can be used: [poly_add](http://www.codewars.com/kata/570eb07e127ad107270005fe) [poly_multiply](http://www.codewars.com/kata/570eb07e127ad107270005fe)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
