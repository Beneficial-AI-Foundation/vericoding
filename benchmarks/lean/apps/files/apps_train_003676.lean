/-
# Task

Given a binary number, we are about to do some operations on the number. Two types of operations can be here:

* ['I', i, j] : Which means invert the bit from i to j (inclusive).

* ['Q', i] : Answer whether the i'th bit is 0 or 1.

The MSB (most significant bit) is the first bit (i.e. i = `1`). The binary number can contain leading zeroes.

## Example
```python
binary_simulation("0011001100", [['I', 1, 10], ['I', 2, 7], ['Q', 2], ['Q', 1], ['Q', 7], ['Q', 5]]) === [ '0', '1', '1', '0' ];
binary_simulation("1011110111", [['I', 1, 10], ['I', 2, 7], ['Q', 2], ['Q', 1], ['Q', 7], ['Q', 5]]) === [ '0', '0', '0', '1' ];
binary_simulation("1011110111", [['I', 1, 10], ['I', 2, 7]]) === [];
binary_simulation("0000000000", [['I', 1, 10], ['Q', 2]]) ===  ['1'];
```
## Note
* All inputs are valid.
* Please optimize your algorithm to avoid time out.
-/

-- <vc-helpers>
-- </vc-helpers>

def binary_simulation (s : String) (ops : List (List Nat)) : List Char := sorry

def simple_simulate (s : String) (ops : List (List Nat)) : List Char := sorry

theorem binary_simulation_matches_reference (s : String) (ops : List (List Nat)) :
  binary_simulation s ops = simple_simulate s ops := sorry

theorem queries_only_match_original (s : String) (queries : List (List Nat)) 
  (h : ∀ q ∈ queries, q.head! = 2 → q.length = 2) :
  binary_simulation s queries = simple_simulate s queries := sorry

theorem double_inversion_cancels (s : String) :
  let i := 1
  let j := s.length 
  let ops := [[0, i, j], [0, i, j], [1, 1]]
  binary_simulation s ops = [s.get 0] := sorry

/-
info: ['0', '1', '1', '0']
-/
-- #guard_msgs in
-- #eval binary_simulation "0011001100" [["I", 1, 10], ["I", 2, 7], ["Q", 2], ["Q", 1], ["Q", 7], ["Q", 5]]

/-
info: ['0', '0', '0', '1']
-/
-- #guard_msgs in
-- #eval binary_simulation "1011110111" [["I", 1, 10], ["I", 2, 7], ["Q", 2], ["Q", 1], ["Q", 7], ["Q", 5]]

/-
info: ['1']
-/
-- #guard_msgs in
-- #eval binary_simulation "0000000000" [["I", 1, 10], ["Q", 2]]

-- Apps difficulty: introductory
-- Assurance level: unguarded