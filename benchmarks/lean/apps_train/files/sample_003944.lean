*** Nova polynomial multiply*** 

This kata is from a series on polynomial handling. ( [#1](http://www.codewars.com/kata/nova-polynomial-1-add-1)   [#2](http://www.codewars.com/kata/570eb07e127ad107270005fe)  [#3](http://www.codewars.com/kata/5714041e8807940ff3001140 )   [#4](http://www.codewars.com/kata/571a2e2df24bdfd4e20001f5))

Consider a polynomial in a list where each element in the list element corresponds to the factors. The factor order is the position in the list. The first element is the zero order factor (the constant).

p = [a0, a1, a2, a3] signifies the polynomial a0 + a1x + a2x^2 + a3*x^3

In this kata multiply two polynomials:

```python 
poly_multiply([1, 2], [1] ) = [1, 2]
poly_multiply([2, 4], [4, 5] ) = [8, 26, 20]
```
The first kata of this series is preloaded in the code and can be used: [poly_add](http://www.codewars.com/kata/nova-polynomial-1-add-1)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible