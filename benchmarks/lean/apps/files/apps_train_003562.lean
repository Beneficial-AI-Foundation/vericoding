/-
The Binomial Form of a polynomial has many uses, just as the standard form does.  For comparison, if p(x) is in Binomial Form and q(x) is in standard form, we might write

p(x) := a0 \* xC0 + a1 \* xC1 + a2 \* xC2 + ... + aN \* xCN

q(x) := b0 + b1 \* x + b2 \* x^(2) + ... + bN \* x^(N)

Both forms have tricks for evaluating them, but tricks should not be necessary.  The most important thing to keep in mind is that aCb can be defined for non-integer values of a; in particular,

```
aCb := a * (a-1) * (a-2) * ... * (a-b+1) / b!   // for any value a and integer values b
    := a! / ((a-b)!b!)                          // for integer values a,b
```

The inputs to your function are an array which specifies a polynomial in Binomial Form, ordered by highest-degree-first, and also a number to evaluate the polynomial at.  An example call might be

```python
value_at([1, 2, 7], 3)
```

and the return value would be 16, since 3C2 + 2 * 3C1 + 7 = 16.  In more detail, this calculation looks like

```
1 * xC2 + 2 * xC1 + 7 * xC0 :: x = 3
3C2 + 2 * 3C1 + 7
3 * (3-1) / 2! + 2 * 3 / 1! + 7
3 + 6 + 7 = 16
```

More information can be found by reading about [Binomial Coefficients](https://en.wikipedia.org/wiki/Binomial_coefficient) or about [Finite Differences](https://en.wikipedia.org/wiki/Finite_difference).

Note that while a solution should be able to handle non-integer inputs and get a correct result, any solution should make use of rounding to two significant digits (as the official solution does) since high precision for non-integers is not the point here.
-/

def value_at (poly: List Int) (x: Float) : Float := sorry

def aCb (a: Float) (b: Int) : Float := sorry

-- <vc-helpers>
-- </vc-helpers>

def intToFloat (i: Int) : Float := sorry

theorem value_at_results_finite (poly: List Int) (x: Float) (h1: poly.length > 0)
  (h2: -10 ≤ x ∧ x ≤ 10) : ∃ (y: Float), value_at poly x = y := sorry

theorem aCb_matches_binomial (a b: Int) (h1: 0 ≤ a ∧ a ≤ 10) (h2: 0 ≤ b ∧ b ≤ 10) 
  (h3: b ≤ a) : ∃ (y: Float), aCb (intToFloat a) b = y := sorry

theorem aCb_results_finite (a: Float) (b: Int) (h1: -10 ≤ a ∧ a ≤ 10) 
  (h2: 0 ≤ b ∧ b ≤ 5) : ∃ (y: Float), aCb a b = y := sorry

theorem value_at_constant (c: Int) (h1: -10 ≤ c ∧ c ≤ 10) :
  (value_at [c] 123 - intToFloat c) < 0.01 ∧ (intToFloat c - value_at [c] 123) < 0.01 := sorry

/-
info: 16
-/
-- #guard_msgs in
-- #eval value_at [1, 2, 7] 3

/-
info: 12
-/
-- #guard_msgs in
-- #eval value_at [1, 2, 7, 0, 5] 2

/-
info: 4.24
-/
-- #guard_msgs in
-- #eval value_at [1, 2, 7, 0, 5] 0.6

-- Apps difficulty: introductory
-- Assurance level: unguarded