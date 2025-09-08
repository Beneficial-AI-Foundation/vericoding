/-
Let us define two functions f and g on positive integer numbers.  $f(n) = \text{product of non-zero digits of} n$

$g(n) = \left\{\begin{array}{ll}{n} & {\text{if} n < 10} \\{g(f(n))} & {\text{otherwise}} \end{array} \right.$ 

You need to process Q queries. In each query, you will be given three integers l, r and k. You need to print the number of integers x between l and r inclusive, such that g(x) = k. 

-----Input-----

The first line of the input contains an integer Q (1 ≤ Q ≤ 2 × 10^5) representing the number of queries. 

Q lines follow, each of which contains 3 integers l, r and k (1 ≤ l ≤ r ≤ 10^6, 1 ≤ k ≤ 9).

-----Output-----

For each query, print a single line containing the answer for that query.

-----Examples-----
Input
4
22 73 9
45 64 6
47 55 7
2 62 4

Output
1
4
0
8

Input
4
82 94 6
56 67 4
28 59 9
39 74 4

Output
3
1
1
5

-----Note-----

In the first example:  g(33) = 9 as g(33) = g(3 × 3) = g(9) = 9  g(47) = g(48) = g(60) = g(61) = 6  There are no such integers between 47 and 55.  g(4) = g(14) = g(22) = g(27) = g(39) = g(40) = g(41) = g(58) = 4
-/

def getSpecialValue : Nat → Nat := 
  fun n => sorry

-- <vc-helpers>
-- </vc-helpers>

def countNumbersWithSpecialValue : List (Nat × Nat × Nat) → List Nat := 
  fun queries => sorry

theorem special_value_counts_correct {l r k : Nat} (h1 : l > 0) (h2 : r > l) (h3 : k > 0) (h4 : k ≤ 9) : 
  let count := (countNumbersWithSpecialValue [(l,r,k)]).head!;
  count = ((List.range (r-l+1)).filter (fun x => getSpecialValue (x + l) = k)).length := by
  sorry

theorem result_list_length_matches_queries {queries : List (Nat × Nat × Nat)} (h : queries.length > 0) :
  (countNumbersWithSpecialValue queries).length = queries.length := by
  sorry

theorem results_are_nonnegative {queries : List (Nat × Nat × Nat)} (h : queries.length > 0) :
  List.all (countNumbersWithSpecialValue queries) (fun x => x ≥ 0) := by
  sorry

/-
info: [1, 4, 0, 8]
-/
-- #guard_msgs in
-- #eval count_numbers_with_special_value [(22, 73, 9), (45, 64, 6), (47, 55, 7), (2, 62, 4)]

/-
info: [3, 1, 1, 5]
-/
-- #guard_msgs in
-- #eval count_numbers_with_special_value [(82, 94, 6), (56, 67, 4), (28, 59, 9), (39, 74, 4)]

-- Apps difficulty: competition
-- Assurance level: unguarded