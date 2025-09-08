/-
Bob is preparing to pass IQ test. The most frequent task in this test is `to find out which one of the given numbers differs from the others`. Bob observed that one number usually differs from the others in **evenness**. Help Bob — to check his answers, he needs a program that among the given numbers finds one that is different in evenness, and return a position of this number.

`!` Keep in mind that your task is to help Bob solve a `real IQ test`, which means indexes of the elements start from `1 (not 0)`

##Examples :

```python
iq_test("2 4 7 8 10") => 3 // Third number is odd, while the rest of the numbers are even

iq_test("1 2 1 1") => 2 // Second number is even, while the rest of the numbers are odd
```
-/

-- <vc-helpers>
-- </vc-helpers>

def iq_test (input : String) : Nat :=
  sorry

theorem iq_test_edge_position_start :
  iq_test "1 2 2 2" = 1 ∧ 
  iq_test "2 1 1 1" = 1 :=
sorry

theorem iq_test_edge_position_end :
  iq_test "2 2 2 1" = 4 ∧
  iq_test "1 1 1 2" = 4 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval iq_test "2 4 7 8 10"

/-
info: 2
-/
-- #guard_msgs in
-- #eval iq_test "1 2 1 1"

/-
info: 3
-/
-- #guard_msgs in
-- #eval iq_test "5 3 2"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible