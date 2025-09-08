/-
You will receive an uncertain amount of integers in a certain order ```k1, k2, ..., kn```.

You form a new number of n digits in the following way:
you take one of the possible digits of the first given number, ```k1```, then the same with the given number ```k2```, repeating the same process up to ```kn``` and you concatenate these obtained digits(in the order that were taken) obtaining the new number. As you can see, we have many possibilities.

Let's see the process above explained with three given numbers:
```
k1 = 23, k2 = 17, k3 = 89
Digits Combinations   Obtained Number
  ('2', '1', '8')           218    <---- Minimum
  ('2', '1', '9')           219
  ('2', '7', '8')           278
  ('2', '7', '9')           279
  ('3', '1', '8')           318
  ('3', '1', '9')           319
  ('3', '7', '8')           378
  ('3', '7', '9')           379    <---- Maximum
             Total Sum =   2388   (8 different values)
```
We need the function that may work in this way:

```python
proc_seq(23, 17, 89) == [8, 218, 379, 2388]
```

See this special case and deduce how the function should handle the cases which have many repetitions.

```python
proc_seq(22, 22, 22, 22) == [1, 2222] # we have only one obtained number, the minimum, maximum and total sum coincide
```

The sequence of numbers will have numbers of n digits only. Numbers formed by leading zeroes will be discarded.

```python
proc_seq(230, 15, 8) == [4, 218, 358, 1152]
```

Enjoy it!!

You will never receive the number 0 and all the numbers will be in valid format.
-/

def proc_seq : List Nat → List Nat 
  | xs => sorry

-- <vc-helpers>
-- </vc-helpers>

def countPermNoLeadingZero (n : Nat) (m : Nat) : Nat :=
  sorry

theorem proc_seq_valid_output (nums : List Nat) :
  let result := proc_seq nums
  (result.length = 2 ∨ result.length = 4) ∧
  (∀ x ∈ result, x ≥ 0) ∧
  (result.length = 2 → result.head! = 1) ∧
  (result.length = 4 → 
    result[1]! ≤ result[2]! ∧ result[1]! ≤ result[3]!) := sorry

theorem proc_seq_leading_zeros (n : Nat) (h : n ≥ 100 ∧ n ≤ 999) :
  let result := proc_seq [n, 0]
  result.head! = countPermNoLeadingZero n 0 := sorry

theorem proc_seq_small_nums {nums : List Nat} (h : 2 ≤ nums.length ∧ nums.length ≤ 3)
  (h' : ∀ n ∈ nums, 1 ≤ n ∧ n ≤ 9) :
  let result := proc_seq nums
  (result.length = 2 ∨ result.length = 4) ∧
  (∀ x ∈ result, x ≥ 0) ∧
  (result.length = 2 → result.head! = 1) ∧
  (result.length = 4 → 
    result[1]! ≤ result[2]! ∧ result[1]! ≤ result[3]!) := sorry

/-
info: [8, 218, 379, 2388]
-/
-- #guard_msgs in
-- #eval proc_seq 23 17 89

/-
info: [1, 2222]
-/
-- #guard_msgs in
-- #eval proc_seq 22 22 22 22

/-
info: [4, 218, 358, 1152]
-/
-- #guard_msgs in
-- #eval proc_seq 230 15 8

-- Apps difficulty: introductory
-- Assurance level: unguarded