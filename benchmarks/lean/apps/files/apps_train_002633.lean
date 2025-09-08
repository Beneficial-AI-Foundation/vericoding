/-
The number `198` has the property that `198 = 11 + 99 + 88, i.e., if each of its digits is concatenated twice and then summed, the result will be the original number`. It turns out that `198` is the only number with this property. However, the property can be generalized so that each digit is concatenated `n` times and then summed. 

eg:-
```
original number =2997 , n=3
2997 = 222+999+999+777 and here each digit is concatenated three times.

original number=-2997 , n=3

-2997 = -222-999-999-777 and here each digit is concatenated three times.

```
Write afunction named `check_concatenated_sum` that tests if a number has this generalized property.
-/

-- <vc-helpers>
-- </vc-helpers>

def checkConcatenatedSum (n : Int) (r : Int) : Bool :=
  sorry

theorem non_positive_repeat_is_false {n r : Int} 
  (h : r ≤ 0) : checkConcatenatedSum n r = false :=
  sorry

theorem check_symmetry {n r : Int}
  (h : r > 0) (h2 : r ≤ 10) :
  checkConcatenatedSum n r = checkConcatenatedSum (-n) r :=
  sorry

theorem zero_is_true {r : Int}
  (h : r > 0) (h2 : r ≤ 10) :
  checkConcatenatedSum 0 r = true :=
  sorry

theorem large_sum_is_false {n r : Int}
  (h_pos : n > 0) (h_r : r > 1) (h_r2 : r ≤ 10)
  (digitSum : Nat)
  (h_sum : digitSum > 1)
  (h_digits : digitSum = sorry) :
  checkConcatenatedSum n r = false :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval check_concatenated_sum 2997 3

/-
info: True
-/
-- #guard_msgs in
-- #eval check_concatenated_sum -198 2

/-
info: False
-/
-- #guard_msgs in
-- #eval check_concatenated_sum 198 0

-- Apps difficulty: introductory
-- Assurance level: unguarded