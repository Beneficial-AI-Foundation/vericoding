/-
This kata focuses on the Numpy python package and you can read up on the Numpy array manipulation functions here: https://docs.scipy.org/doc/numpy-1.13.0/reference/routines.array-manipulation.html

You will get two integers `N` and `M`. You must return an array with two sub-arrays with numbers in ranges `[0, N / 2)` and `[N / 2, N)` respectively, each of them being rotated `M` times.

```
reorder(10, 1)   =>  [[4, 0, 1, 2, 3], [9, 5, 6, 7, 8]]
reorder(10, 3)   =>  [[2, 3, 4, 0, 1], [7, 8, 9, 5, 6]]
reorder(10, 97)  =>  [[3, 4, 0, 1, 2], [8, 9, 5, 6, 7]]
```
-/

-- <vc-helpers>
-- </vc-helpers>

def reorder (n : Nat) (m : Nat) : (List Nat × List Nat) :=
  sorry

theorem reorder_output_size {n m : Nat} (h : 2 ∣ n) (h2 : n ≥ 2) :
  let result := reorder n m
  List.length result.1 = n/2 ∧ List.length result.2 = n/2 :=
sorry

theorem reorder_partitions {n m : Nat} (h : 2 ∣ n) (h2 : n ≥ 2) :
  let result := reorder n m
  let flattened := result.1 ++ result.2
  List.Perm flattened (List.range n) :=
sorry

theorem reorder_mod_equiv {n m : Nat} (h : 2 ∣ n) (h2 : n ≥ 2) :
  reorder n m = reorder n (m % (n/2)) :=
sorry

theorem reorder_halves_bound {n m : Nat} (h : 2 ∣ n) (h2 : n ≥ 2) :
  let result := reorder n m
  (∀ x ∈ result.1, x < n/2) ∧ 
  (∀ x ∈ result.2, x ≥ n/2) :=
sorry

/-
info: [[4, 0, 1, 2, 3], [9, 5, 6, 7, 8]]
-/
-- #guard_msgs in
-- #eval reorder 10 1

/-
info: [[2, 3, 4, 0, 1], [7, 8, 9, 5, 6]]
-/
-- #guard_msgs in
-- #eval reorder 10 3

/-
info: [[3, 4, 0, 1, 2], [8, 9, 5, 6, 7]]
-/
-- #guard_msgs in
-- #eval reorder 10 97

-- Apps difficulty: introductory
-- Assurance level: unguarded