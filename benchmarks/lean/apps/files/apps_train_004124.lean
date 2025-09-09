/-
One of the first algorithm used for approximating the integer square root of a positive integer `n` is known as "Hero's method", 
named after the first-century Greek mathematician Hero of Alexandria who gave the first description
of the method. Hero's method can be obtained from Newton's method which came 16 centuries after. 

We approximate the square root of a number `n` by taking an initial guess `x`, an error `e` and repeatedly calculating a new approximate *integer* value `x` using: `(x + n / x) / 2`; we are finished when the previous `x` and the `new x` have an absolute difference less than `e`.

We supply to a function (int_rac) a number `n` (positive integer) and a parameter `guess` (positive integer) which will be our initial `x`. For this kata the parameter 'e' is set to `1`.

Hero's algorithm is not always going to come to an exactly correct result! For instance: if n = 25 we get 5 but for n = 26 we also get 5. Nevertheless `5` is the *integer* square root of `26`.

The kata is to return the count of the progression of integer approximations that the algorithm makes.

Reference:

Some examples:
```
int_rac(25,1): follows a progression of [1,13,7,5] so our function should return 4.

int_rac(125348,300): has a progression of [300,358,354] so our function should return 3.

int_rac(125348981764,356243): has a progression of [356243,354053,354046] so our function should return 3.
```

#

You can use Math.floor (or similar) for each integer approximation.

#

Note for JavaScript, Coffescript, Typescript:

Don't use the double bitwise NOT ~~ at each iteration if you want to have the same results as in the tests and the other languages.
-/

-- <vc-helpers>
-- </vc-helpers>

def int_rac (n : Nat) (guess : Nat) : Nat :=
  sorry

theorem int_rac_perfect_squares_consistency (x : Nat)
  (h1 : x ≥ 1) (h2 : x ≤ 20) :
  let n := x * x
  let guess1 := max 1 (x - 1) 
  let guess2 := x + 1
  Nat.sub (int_rac n guess1) (int_rac n guess2) ≤ 1 ∧ 
  Nat.sub (int_rac n guess2) (int_rac n guess1) ≤ 1 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval int_rac 25 1

/-
info: 3
-/
-- #guard_msgs in
-- #eval int_rac 125348 300

/-
info: 3
-/
-- #guard_msgs in
-- #eval int_rac 125348981764 356243

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible