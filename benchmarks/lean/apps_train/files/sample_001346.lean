/-
Chef has a sequence $A_1, A_2, \ldots, A_N$. For a positive integer $M$, sequence $B$ is defined as $B = A*M$ that is, appending $A$ exactly $M$ times. For example, If $A = [1, 2]$ and $M = 3$, then $B = A*M = [1, 2, 1, 2, 1, 2]$
You have to help him to find out the minimum value of $M$ such that the length of the longest strictly increasing subsequence is maximum possible.

-----Input:-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output:-----
For each test case, print a single line containing one integer ― the minimum value of $M$.

-----Constraints-----
- $1 \le T \le 500$
- $1 \le N \le 2*10^5$
- $1 \le A_i \le 10^9$
- It's guaranteed that the total length of the sequence $A$ in one test file doesn't exceed $2*10^6$

-----Sample Input:-----
3
2
2 1
2
1 2
5
1 3 2 1 2

-----Sample Output:-----
2
1
2

-----Explanation:-----
In the first test case, Choosing $M = 2$ gives $B = [2, 1, 2, 1]$ which has a longest strictly increasing sequence of length $2$ which is the maximum possible.
In the second test case, Choosing $M = 1$ gives $B  = [1, 2]$ which has a longest strictly increasing sequence of length $2$ which is the maximum possible.
-/

def find_min_m (arr : List Int) (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def countUnique (arr : List Int) : Nat :=
  (arr.eraseDups).length

theorem find_min_m_bounds (arr : List Int) (n : Nat) (h : n = arr.length) :
  1 ≤ find_min_m arr n ∧ find_min_m arr n ≤ countUnique arr := by
  sorry

theorem find_min_m_single_element (arr : List Int) (h : arr.length = 1) :
  find_min_m arr arr.length = 1 := by
  sorry

theorem find_min_m_sorted (arr : List Int) (h : arr.length ≥ 2) :
  find_min_m (List.mergeSort (·≤·) arr) arr.length = 1 := by
  sorry

theorem find_min_m_reverse_sorted (arr : List Int) (h : arr.length ≥ 2) :
  find_min_m (List.mergeSort (·≥·) arr) arr.length = countUnique arr := by
  sorry

theorem find_min_m_small_range (arr : List Int) 
  (h₁ : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 3)
  (h₂ : arr.length ≥ 1)
  (h₃ : arr.length ≤ 10) :
  1 ≤ find_min_m arr arr.length ∧ find_min_m arr arr.length ≤ countUnique arr := by
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_min_m [2, 1] 2

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_min_m [1, 2] 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_min_m [1, 3, 2, 1, 2] 5

-- Apps difficulty: interview
-- Assurance level: unguarded