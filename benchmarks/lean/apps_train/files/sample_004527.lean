*** Nova polynomial derivative*** 

This kata is from a series on polynomial handling. ( [#1](http://www.codewars.com/kata/nova-polynomial-1-add-1)   [#2](http://www.codewars.com/kata/570eb07e127ad107270005fe)  [#3](http://www.codewars.com/kata/5714041e8807940ff3001140 )   [#4](http://www.codewars.com/kata/571a2e2df24bdfd4e20001f5))

Consider a polynomial in a list where each element in the list element corresponds to the factors. The factor order is the position in the list. The first element is the zero order factor (the constant).

p = [a0, a1, a2, a3] signifies the polynomial a0 + a1x + a2x^2 + a3*x^3

In this kata return the derivative of a polynomial:

```python 
poly_derivative([1, 2] ) = [2]
poly_derivative([9, 1, 3]) =  [1, 6]
```

Previous Katas on Nova polynomial:

 1. [poly_add](http://www.codewars.com/kata/nova-polynomial-1-add-1) 
 2. [poly_multiply](http://www.codewars.com/kata/570eb07e127ad107270005fe).
 3. [poly_subtract](http://www.codewars.com/kata/5714041e8807940ff3001140 )

def poly_derivative (p : List Int) : List Int :=
  sorry

def scaleList (k : Int) (xs : List Int) : List Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible