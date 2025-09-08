/-
We have an array of unique elements. A special kind of permutation is the one that has all of its elements in a different position than the original.

Let's see how many of these permutations may be generated from an array of four elements. We put the original array with square brackets and the wanted permutations with parentheses. 
```
arr = [1, 2, 3, 4]
      (2, 1, 4, 3)
      (2, 3, 4, 1)
      (2, 4, 1, 3)
      (3, 1, 4, 2)
      (3, 4, 1, 2)
      (3, 4, 2, 1)
      (4, 1, 2, 3)
      (4, 3, 1, 2)
      (4, 3, 2, 1)
      _____________
A total of 9 permutations with all their elements in different positions than arr
```

The task for this kata would be to create a code to count all these permutations for an array of certain length.

Features of the random tests:
```
l = length of the array
10 ≤ l ≤ 5000
```

See the example tests.

Enjoy it!
-/

-- <vc-helpers>
-- </vc-helpers>

def all_permuted (n : Nat) : Nat := sorry

theorem all_permuted_nonnegative (n : Nat) : 
  all_permuted n ≥ 0 :=
sorry

theorem all_permuted_base_cases : 
  all_permuted 1 = 0 ∧ all_permuted 2 = 1 :=
sorry

theorem all_permuted_increases (n : Nat) :
  n > 2 → all_permuted n > all_permuted (n-1) :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval all_permuted 1

/-
info: 9
-/
-- #guard_msgs in
-- #eval all_permuted 4

/-
info: 97581073836835777732377428235481
-/
-- #guard_msgs in
-- #eval all_permuted 30

-- Apps difficulty: introductory
-- Assurance level: unguarded