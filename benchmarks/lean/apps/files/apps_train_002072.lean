/-
A function $f : R \rightarrow R$ is called Lipschitz continuous if there is a real constant K such that the inequality |f(x) - f(y)| ≤ K·|x - y| holds for all $x, y \in R$. We'll deal with a more... discrete version of this term.

For an array $h [ 1 . . n ]$, we define it's Lipschitz constant $L(h)$ as follows:  if n < 2, $L(h) = 0$  if n ≥ 2, $L(h) = \operatorname{max} [ \frac{|h [ j ] - h [ i ]|}{j - i} ]$ over all 1 ≤ i < j ≤ n 

In other words, $L = L(h)$ is the smallest non-negative integer such that |h[i] - h[j]| ≤ L·|i - j| holds for all 1 ≤ i, j ≤ n.

You are given an array [Image] of size n and q queries of the form [l, r]. For each query, consider the subarray $s = a [ l . . r ]$; determine the sum of Lipschitz constants of all subarrays of $S$.

-----Input-----

The first line of the input contains two space-separated integers n and q (2 ≤ n ≤ 100 000 and 1 ≤ q ≤ 100) — the number of elements in array [Image] and the number of queries respectively.

The second line contains n space-separated integers $a [ 1 . . n ]$ ($0 \leq a [ i ] \leq 10^{8}$).

The following q lines describe queries. The i-th of those lines contains two space-separated integers l_{i} and r_{i} (1 ≤ l_{i} < r_{i} ≤ n).

-----Output-----

Print the answers to all queries in the order in which they are given in the input. For the i-th query, print one line containing a single integer — the sum of Lipschitz constants of all subarrays of [Image].

-----Examples-----
Input
10 4
1 5 2 9 1 3 4 2 1 7
2 4
3 8
7 10
1 9

Output
17
82
23
210

Input
7 6
5 7 7 4 6 6 2
1 2
2 3
2 6
1 7
4 7
3 5

Output
2
0
22
59
16
8

-----Note-----

In the first query of the first sample, the Lipschitz constants of subarrays of $[ 5,2,9 ]$ with length at least 2 are:  $L([ 5,2 ]) = 3$  $L([ 2,9 ]) = 7$  $L([ 5,2,9 ]) = 7$ 

The answer to the query is their sum.
-/

def compute_lipschitz_sums (arr : List Nat) (queries : List (Nat × Nat)) : List Nat :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def sort (l : List Nat) : List Nat :=
sorry

theorem array_properties {arr : List Nat} (h: arr.length ≥ 2)
  (hb: ∀ x, x ∈ arr → x ≤ 10^8) :
  let result := compute_lipschitz_sums arr [(1, arr.length)]
  result.length = 1 ∧ 
  ∀ x, x ∈ result → x ≥ 0 :=
sorry

theorem constant_array_sums {arr : List Nat} {queries : List (Nat × Nat)}
  (h: arr.length ≥ 2)
  (hconst: ∀ (i j : Fin arr.length), arr[i] = arr[j])
  (hq: ∀ p, p ∈ queries → p.1 ≤ p.2 ∧ p.2 ≤ arr.length) :
  ∀ x, x ∈ compute_lipschitz_sums arr queries → x = 0 :=
sorry

theorem query_bounds_valid {arr : List Nat} {queries : List (Nat × Nat)}
  (h: arr.length ≥ 2)
  (hq: ∀ p, p ∈ queries → p.1 ≤ p.2 ∧ p.2 ≤ arr.length) :
  let results := compute_lipschitz_sums arr queries
  results.length = queries.length :=
sorry

theorem monotonic_increasing_minimal {arr : List Nat} 
  (h: arr.length ≥ 2)
  (hb: ∀ x, x ∈ arr → x ≤ 10) :
  let sorted := sort arr
  let orig_sum := (compute_lipschitz_sums arr [(1, arr.length)]).head!
  let sorted_sum := (compute_lipschitz_sums sorted [(1, arr.length)]).head!
  sorted_sum ≤ orig_sum :=
sorry

/-
info: [17, 82, 23, 210]
-/
-- #guard_msgs in
-- #eval compute_lipschitz_sums [1, 5, 2, 9, 1, 3, 4, 2, 1, 7] [(2, 4), (3, 8), (7, 10), (1, 9)]

/-
info: [2, 0, 22, 59, 16, 8]
-/
-- #guard_msgs in
-- #eval compute_lipschitz_sums [5, 7, 7, 4, 6, 6, 2] [(1, 2), (2, 3), (2, 6), (1, 7), (4, 7), (3, 5)]

/-
info: [100000000, 100000000]
-/
-- #guard_msgs in
-- #eval compute_lipschitz_sums [100000000, 0] [(1, 2), (1, 2)]

-- Apps difficulty: competition
-- Assurance level: guarded