/-
There are $n$ positive integers $a_1, a_2, \dots, a_n$. For the one move you can choose any even value $c$ and divide by two all elements that equal $c$.

For example, if $a=[6,8,12,6,3,12]$ and you choose $c=6$, and $a$ is transformed into $a=[3,8,12,3,3,12]$ after the move.

You need to find the minimal number of moves for transforming $a$ to an array of only odd integers (each element shouldn't be divisible by $2$).

-----Input-----

The first line of the input contains one integer $t$ ($1 \le t \le 10^4$) — the number of test cases in the input. Then $t$ test cases follow.

The first line of a test case contains $n$ ($1 \le n \le 2\cdot10^5$) — the number of integers in the sequence $a$. The second line contains positive integers $a_1, a_2, \dots, a_n$ ($1 \le a_i \le 10^9$).

The sum of $n$ for all test cases in the input doesn't exceed $2\cdot10^5$.

-----Output-----

For $t$ test cases print the answers in the order of test cases in the input. The answer for the test case is the minimal number of moves needed to make all numbers in the test case odd (i.e. not divisible by $2$).

-----Example-----
Input
4
6
40 6 40 3 20 1
1
1024
4
2 4 8 16
3
3 1 7

Output
4
10
4
0

-----Note-----

In the first test case of the example, the optimal sequence of moves can be as follows:

  before making moves $a=[40, 6, 40, 3, 20, 1]$;  choose $c=6$;  now $a=[40, 3, 40, 3, 20, 1]$;  choose $c=40$;  now $a=[20, 3, 20, 3, 20, 1]$;  choose $c=20$;  now $a=[10, 3, 10, 3, 10, 1]$;  choose $c=10$;  now $a=[5, 3, 5, 3, 5, 1]$ — all numbers are odd. 

Thus, all numbers became odd after $4$ moves. In $3$ or fewer moves, you cannot make them all odd.
-/

-- <vc-helpers>
-- </vc-helpers>

def min_moves_to_odd (arrays : List (List Nat)) : List Nat := sorry

def countTrailingZeros (n : Nat) : Nat := sorry

theorem result_same_length_as_input (arrays : List (List Nat)) :
  List.length (min_moves_to_odd arrays) = List.length arrays :=
  sorry

theorem result_is_non_negative (arrays : List (List Nat)) :
  ∀ x ∈ min_moves_to_odd arrays, x ≥ 0 :=
  sorry

/-
info: [4]
-/
-- #guard_msgs in
-- #eval min_moves_to_odd [[40, 6, 40, 3, 20, 1]]

/-
info: [10]
-/
-- #guard_msgs in
-- #eval min_moves_to_odd [[1024]]

/-
info: [4]
-/
-- #guard_msgs in
-- #eval min_moves_to_odd [[2, 4, 8, 16]]

/-
info: [0]
-/
-- #guard_msgs in
-- #eval min_moves_to_odd [[3, 1, 7]]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible