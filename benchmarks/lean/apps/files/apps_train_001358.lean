/-
Chef solved so many hard questions, now he wants to solve some easy problems for refreshment. Chef asks Cheffina for the new question. Cheffina challanges the chef to print the total number of 1's in the binary representation of N(natural number).

-----Input:-----
- First-line will contain $T$, the number of test cases. Then the test cases follow. 
- Each test case contains a single line of input, $N$. 

-----Output:-----
For each test case, output in a single line answer.

-----Constraints-----
- $1 \leq T \leq 10^6$
- $1 \leq N \leq 10^6$

-----Sample Input:-----
2
2
5

-----Sample Output:-----
1
2

-----EXPLANATION:-----
For 1) Binary representation of 2 is 10. i.e. only one 1 present in it.
For 2) Binary representation of 5 is 101, i.e. two 1's present in it.
-/

def count_ones_in_binary (n : Int) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def count_bits : Int → Nat :=
  fun n => if n = 0 then 0 else (n % 2).natAbs + count_bits (n / 2)
decreasing_by sorry

theorem count_ones_nonnegative_basic {x : Int} (h : x ≥ 0) :
  count_ones_in_binary x ≥ 0 :=
  sorry

theorem count_ones_negative_has_ones {x : Int} (h : x < 0) :
  count_ones_in_binary x > 0 :=
  sorry

theorem count_ones_power_of_two {x : Int} (h1 : x > 0) (h2 : x % 2 = 0) :
  count_ones_in_binary x = 1 :=
  sorry

theorem count_ones_equals_bit_count {x : Int} (h : x ≥ 0) :
  count_ones_in_binary x = count_bits x :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_ones_in_binary test_input[0]

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_ones_in_binary test_input[0]

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_ones_in_binary test_input[0]

-- Apps difficulty: interview
-- Assurance level: unguarded