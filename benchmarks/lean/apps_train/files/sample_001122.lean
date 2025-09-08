/-
Chef is an advocate for Go Green Initiative. Today he had n trees planted in a row outside his his restaurant. Today, the height of i-th tree is hi feet. The trees grow at a rate of mi feet per day.
Chef knows that trees will look beautiful if they form a zig-zag sequence. The trees will be said to be in Zig-zag sequence if the heights of tree first increases or decreases, then alternates between decreasing/increasing respectively. Formally, the trees will be said to in Zig-zag sequence if one of the following two conditions holds.

- h1 < h2 > h3 < h4 and so on..
- h1 >  h2 < h3 > h4 and so on..

Chef wants to know intervals of time when the heights of the trees will form a zig-zag sequence.

-----Input-----
The first line of the input contains an integer T denoting the number of test cases. The description of T test cases follows.
The first line of each test case contains a single integer n, denoting the number of trees.
The ith of following N lines contains two space separated integers hi and mi, denoting the initial height and the growth speed for ith tree.

-----Output-----
For each test case, output an integer Q - the amount of the periods of consecutive moments of time, when the trees for a zig-zag sequence.
On the following Q lines, output the intervals of time when the trees' heights form a zig-zag sequence. For each intervals, output its' smallest and the largest instants of time. If the range is infinite, output Inf as the right bound.
The test cases are designed in such a way that the total output won't exceed 2 MB.

-----Constraints-----

- 1 ≤ T ≤ 105
- 1 ≤ n ≤ 10
- Subtask 1 (23 points): 0 ≤ hi, mi ≤ 10
- Subtask 2 (77 points): 0 ≤ hi, mi ≤ 109
- 1 ≤ sum of n over a test cases in a single test file ≤ 5 × 105

-----Example-----
Input:3
3
0 1
2 2
0 3
2
2 1
1 2
3
1 1
2 2
3 3

Output:1
0 1
2
0 0
2 Inf
0

-----Explanation-----
Example case 1. In the first case 0 2 0 is already a zig-zag sequence, but on the 2nd second it will become 2 6 6 and will never turn back into zig-zag
-/

-- <vc-helpers>
-- </vc-helpers>

def find_zigzag_intervals (trees : List (Int × Int)) : List (Nat × (Nat ⊕ Unit)) :=
  sorry

theorem output_format (trees : List (Int × Int)) :
  let result := find_zigzag_intervals trees
  (∀ interval ∈ result,
    ∃ (start : Nat) (endVal : Nat ⊕ Unit),
      interval = (start, endVal) ∧
      (match endVal with
        | Sum.inl n => n ≥ start
        | Sum.inr _ => True)) :=
  sorry

theorem single_tree (tree : Int × Int) :
  find_zigzag_intervals [tree] = [(0, Sum.inr ())] :=
  sorry

theorem sorted_intervals (trees : List (Int × Int)) :
  let result := find_zigzag_intervals trees
  ∀ (i j : Nat),
    i < j →
    j < result.length →
    i < result.length →
    ∀ (n : Nat) (start : Nat),
    (result.get! i).2 = Sum.inl n →
    (result.get! j).1 = start →
    n < start :=
  sorry

theorem interval_bounds (trees : List (Int × Int)) :
  let result := find_zigzag_intervals trees
  ∀ interval ∈ result,
    match interval with
    | (start, Sum.inl endVal) => 0 ≤ start ∧ start ≤ endVal ∧ endVal < 10^20
    | (start, Sum.inr _) => 0 ≤ start :=
  sorry

/-
info: [(0, 1)]
-/
-- #guard_msgs in
-- #eval find_zigzag_intervals [(0, 1), (2, 2), (0, 3)]

/-
info: [(0, 0), (2, 'Inf')]
-/
-- #guard_msgs in
-- #eval find_zigzag_intervals [(2, 1), (1, 2)]

/-
info: []
-/
-- #guard_msgs in
-- #eval find_zigzag_intervals [(1, 1), (2, 2), (3, 3)]

-- Apps difficulty: interview
-- Assurance level: unguarded