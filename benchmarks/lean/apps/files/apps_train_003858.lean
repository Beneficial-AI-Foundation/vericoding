/-
I love Fibonacci numbers in general, but I must admit I love some more than others. 

I would like for you to write me a function that when given a number (n)  returns the n-th number in the Fibonacci Sequence.

For example:

```python
   nth_fib(4) == 2
```

Because 2 is the 4th number in the Fibonacci Sequence.

For reference, the first two numbers in the Fibonacci sequence are 0 and 1, and each subsequent number is the sum of the previous two.
-/

-- <vc-helpers>
-- </vc-helpers>

def nth_fib (n : Nat) : Nat :=
  sorry

theorem fib_sum_of_previous (n : Nat) (h : n ≥ 3) : 
  nth_fib n = nth_fib (n-1) + nth_fib (n-2) :=
  sorry

theorem fib_nonnegative (n : Nat) (h : n > 0) :
  nth_fib n ≥ 0 :=
  sorry

theorem fib_first_two : 
  nth_fib 1 = 0 ∧ nth_fib 2 = 1 :=
  sorry

theorem fib_strictly_increasing (n : Nat) (h : n ≥ 4) :
  nth_fib n > nth_fib (n-1) :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval nth_fib 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval nth_fib 4

/-
info: 34
-/
-- #guard_msgs in
-- #eval nth_fib 10

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible