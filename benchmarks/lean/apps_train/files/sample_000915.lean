/-
You are given $N$ integers in an array: $A[1], A[2], \ldots, A[N]$. You also have another integer $L$.
Consider a sequence of indices ($i_1, i_2, \ldots, i_k$). Note that a particular index can occur multiple times in the sequence, and there is no order in which these indices have to occur. ($i_1, i_2, \ldots, i_k$) is a sequence of size $k$. It is said to be an $Interesting$ sequence, if $A[i_1] \ge A[i_2] \ge \ldots \ge A[i_k]$.
The $Cost$ of an Interesting sequence ($i_1, i_2, \ldots, i_k$), is defined to be the minimum absolute difference between any two adjacent indices. In other words, the Cost is $min \{ |i_2 - i_1|, |i_3 - i_2|, \ldots, |i_k - i_{k-1}| \}$.
Your job is to consider the Costs of all the Interesting sequences of size $L$ associated with the given array, and output the maximum Cost. Note that you can show that there is always at least one Interesting sequence for the given constraints.

-----Input-----
- The first line contains a single integer, $T$, which is the number of testcases. The description of each testcase follows.
- The first line of each testcase contains two space separated integers: $N$ and $L$.
- The second line of each testcase contains $N$ space separated integers: $A[1], A[2], \ldots, A[N]$.

-----Output-----
- For each testcase, output the answer in a new line.

-----Constraints-----
- $1 \leq T \leq 3$
- $1 \leq A[i] \leq 10^9$
- $2 \leq L \leq 10^9$

-----Subtasks-----
- Subtask 1: 7 points
- It is guaranteed that $A[1] > A[2] > \ldots > A[N]$
- Note that the above condition implies that all elements are distinct.
- $1 \leq N \leq 500$
- Subtask 2: 7 points
- It is guaranteed that $A[1] \ge A[2] \ge \ldots \ge A[N]$
- $1 \leq N \leq 500$
- Subtask 3: 14 points
- It is guaranteed that all elements are distinct.
- $1 \leq N \leq 500$
- Subtask 4: 14 points
- $1 \leq N \leq 500$
- Subtask 5: 25 points
- It is guaranteed that all elements are distinct.
- $1 \leq N \leq 3000$
- Subtask 6: 33 points
- $1 \leq N \leq 3000$

-----Sample Input-----
1
6 3
2 4 1 12 3 5

-----Sample Output-----
3

-----Explanation-----
We are looking for Interesting sequences of length 3. Some of them are:
- (4, 2, 3): This is Interesting because $A[4] \ge A[2] \ge A[3]$. Its cost is $min \{ |2-4|, |3-2|\} = 1$.
- (5, 1, 1): Cost is 0.
- (2, 2, 2): Cost is 0.
- (6, 1, 3): Cost is 2.
- (6, 2, 5): Cost is 3.
There are other Interesting Sequences of length 3 as well. But if you list them all out, you'll see that the maximum Cost is 3. Hence the answer is 3.
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_interesting_sequence (n : Nat) (l : Nat) (arr : List Nat) : Nat := sorry

theorem sequence_properties {n : Nat} {l : Nat} {arr : List Nat} 
  (hn : n > 0) (hl : l > 0) (harr : arr.length = n) (hbound : ∀ x ∈ arr, x > 0 ∧ x ≤ 100) :
  let result := solve_interesting_sequence n l arr;
  -- Result is non-negative
  result ≥ 0  
  -- Result is bounded by array length
  ∧ result ≤ n
  -- Result is at least the max distance between duplicates
  ∧ ∀ (x : Nat) (pos₁ pos₂ : Nat),
    let indices : List (Nat × Nat) := List.enumFrom 1 arr;
    let positions := List.filterMap (fun p => if p.2 = x then some p.1 else none) indices;
    pos₁ ∈ positions →
    pos₂ ∈ positions →
    pos₁ ≠ pos₂ →
    result ≥ (max pos₁ pos₂ - min pos₁ pos₂) := by sorry

theorem base_case : solve_interesting_sequence 1 1 [5] = 0 := by sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_interesting_sequence 6 3 [2, 4, 1, 12, 3, 5]

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_interesting_sequence 4 2 [5, 5, 5, 5]

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_interesting_sequence 5 3 [1, 2, 3, 4, 5]

-- Apps difficulty: interview
-- Assurance level: unguarded