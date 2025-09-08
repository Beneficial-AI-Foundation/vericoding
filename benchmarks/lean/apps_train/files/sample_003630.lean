/-
Given a certain integer  ```n, n > 0```and a number of partitions,  ```k, k > 0```; we want to know the partition which has the maximum or minimum product of its terms.

The function ```find_spec_partition() ```, will receive three arguments,  ```n```,  ```k```, and a command:  ```'max' or 'min'```

The function should output the partition that has maximum or minimum value product (it depends on the given command) as an array with its terms in decreasing order.

Let's see some cases (Python and Ruby)
```
find_spec_partition(10, 4, 'max') == [3, 3, 2, 2]
find_spec_partition(10, 4, 'min') == [7, 1, 1, 1]
```
and Javascript:
```
findSpecPartition(10, 4, 'max') == [3, 3, 2, 2]
findSpecPartition(10, 4, 'min') == [7, 1, 1, 1]
```
The partitions of 10 with 4 terms with their products are:
```
(4, 3, 2, 1): 24
(4, 2, 2, 2): 32
(6, 2, 1, 1): 12
(3, 3, 3, 1): 27
(4, 4, 1, 1): 16
(5, 2, 2, 1): 20 
(7, 1, 1, 1): 7   <------- min. productvalue
(3, 3, 2, 2): 36  <------- max.product value
(5, 3, 1, 1): 15
```
Enjoy it!
-/

def List.sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + xs.sum

def List.prod : List Nat → Nat 
  | [] => 1
  | x::xs => x * xs.prod

-- <vc-helpers>
-- </vc-helpers>

def find_spec_partition (n k : Nat) (command : String) : List Nat :=
  sorry

theorem find_spec_partition_length (n k : Nat) (h : k ≤ n) :
  ∀ command, command = "max" ∨ command = "min" →
    (find_spec_partition n k command).length = k := sorry

theorem find_spec_partition_positive (n k : Nat) (h : k ≤ n) :
  ∀ command, command = "max" ∨ command = "min" →
    ∀ x, x ∈ find_spec_partition n k command → x > 0 := sorry

theorem find_spec_partition_max_diff (n k : Nat) (h : k ≤ n) :
  let result := find_spec_partition n k "max"
  ∀ x y, x ∈ result → y ∈ result → x - y ≤ 1 := sorry

/-
info: [3, 3, 2, 2]
-/
-- #guard_msgs in
-- #eval find_spec_partition 10 4 "max"

/-
info: [7, 1, 1, 1]
-/
-- #guard_msgs in
-- #eval find_spec_partition 10 4 "min"

/-
info: [3, 3, 2]
-/
-- #guard_msgs in
-- #eval find_spec_partition 8 3 "max"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible