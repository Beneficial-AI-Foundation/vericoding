/-
A string with length $L$ is called rich if $L \ge 3$ and there is a character which occurs in this string strictly more than $L/2$ times.
You are given a string $S$ and you should answer $Q$ queries on this string. In each query, you are given a substring $S_L, S_{L+1}, \ldots, S_R$. Consider all substrings of this substring. You have to determine whether at least one of them is rich.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains two space-separated integers $N$ and $Q$.
- The second line contains a single string $S$ with length $N$.
- Each of the next $Q$ lines contains two space-separated integers $L$ and $R$ describing a query.

-----Output-----
For each query, print a single line containing the string "YES" if the given substring contains a rich substring or "NO" if it does not contain any rich substring.

-----Constraints-----
- $1 \le T \le 10$
- $1 \le N, Q \le 10^5$
- $1 \le L \le R \le N$
- $S$ contains only lowercase English letters

-----Example Input-----
1
10 2
helloworld
1 3
1 10

-----Example Output-----
NO
YES
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_rich_substrings (s : String) (queries : List (Nat × Nat)) : List String :=
  sorry

theorem empty_queries_give_empty_result (s : String) :
  solve_rich_substrings s [] = [] :=
  sorry

theorem too_short_range_always_no (s : String) (queries : List (Nat × Nat)) :
  (∀ q ∈ queries, q.1 = 1 ∧ q.2 = 2) →
  ∀ r ∈ solve_rich_substrings s queries, r = "NO" :=
  sorry 

theorem result_length_matches_queries (s : String) (queries : List (Nat × Nat)) :
  (∀ q ∈ queries, q.1 < q.2 ∧ q.2 ≤ s.length) →
  (solve_rich_substrings s queries).length = queries.length :=
  sorry

theorem results_only_yes_or_no (s : String) (queries : List (Nat × Nat)) :
  (∀ q ∈ queries, q.1 < q.2 ∧ q.2 ≤ s.length) →
  ∀ r ∈ solve_rich_substrings s queries, r = "YES" ∨ r = "NO" :=
  sorry

/-
info: ['NO', 'YES']
-/
-- #guard_msgs in
-- #eval solve_rich_substrings "helloworld" [[1, 3], [1, 10]]

/-
info: ['YES']
-/
-- #guard_msgs in
-- #eval solve_rich_substrings "aaa" [[1, 3]]

/-
info: ['NO']
-/
-- #guard_msgs in
-- #eval solve_rich_substrings "abc" [[1, 3]]

-- Apps difficulty: interview
-- Assurance level: unguarded