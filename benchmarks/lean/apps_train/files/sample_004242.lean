/-
Find the closest prime number under a certain integer ```n``` that has the maximum possible amount of even digits.

For ```n = 1000```, the highest prime under ```1000``` is ```887```, having two even digits (8 twice)

Naming ```f()```, the function that gives that prime, the above case and others will be like the following below.
```
f(1000) ---> 887 (even digits: 8, 8)

f(1210) ---> 1201 (even digits: 2, 0)

f(10000) ---> 8887

f(500) ---> 487

f(487) ---> 467
``` 
Features of the random tests:
```
Number of tests = 28
1000 <= n <= 5000000
```

Enjoy it!!
-/

def f (n : Int) : Int :=
  sorry

def is_prime (n : Int) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def count_even_digits (n : Int) : Nat :=
  sorry

theorem f_result_is_prime (n : Int) (h : n ≥ 2) :
  is_prime (f n) = true ∨ f n = 0 :=
  sorry

theorem f_result_less_than_input (n : Int) (h : n ≥ 2) :
  f n ≤ n :=
  sorry

theorem f_result_has_max_even_digits (n : Int) (h : n ≥ 2) :
  f n ≠ 0 →
  ∀ i : Int, 2 ≤ i → i ≤ n → is_prime i = true →
  count_even_digits i ≤ count_even_digits (f n) :=
  sorry

theorem f_result_largest_for_same_even_digits (n : Int) (h : n ≥ 2) :
  f n ≠ 0 →
  ∀ i : Int, f n < i → i ≤ n → is_prime i = true →
  count_even_digits i = count_even_digits (f n) → False :=
  sorry

theorem f_small_inputs (n : Int) (h : n ≤ 1) :
  f n = 0 :=
  sorry

/-
info: 887
-/
-- #guard_msgs in
-- #eval f 1000

/-
info: 8887
-/
-- #guard_msgs in
-- #eval f 10000

/-
info: 487
-/
-- #guard_msgs in
-- #eval f 500

-- Apps difficulty: introductory
-- Assurance level: guarded