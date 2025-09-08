/-
You are given a sequence of N$N$ powers of an integer k$k$; let's denote the i$i$-th of these powers by kAi$k^{A_i}$. You should partition this sequence into two non-empty contiguous subsequences; each element of the original sequence should appear in exactly one of these subsequences. In addition, the product of (the sum of elements of the left subsequence) and (the sum of elements of the right subsequence) should be maximum possible.
Find the smallest position at which you should split this sequence in such a way that this product is maximized.

-----Input-----
- The first line of the input contains a single integer T$T$ denoting the number of test cases. The description of T$T$ test cases follows.
- The first line of each test case contains two space-separated integers N$N$ and k$k$.
- The second line contains N$N$ space-separated integers A1,A2,…,AN$A_1, A_2, \dots, A_N$.

-----Output-----
For each test case, print a single line containing one integer — the size of the left subsequence. If there is more than one possible answer, print the smallest possible one.

-----Constraints-----
- 1≤T≤10$1 \le T \le 10$
- 2≤N≤105$2 \le N \le 10^5$
- 2≤k≤109$2 \le k \le 10^9$
- 0≤Ai≤105$0 \le A_i \le 10^5$ for each valid i$i$

-----Subtasks-----
Subtask #1 (30 points):
- 2≤N≤1,000$2 \le N \le 1,000$
- 0≤Ai≤1,000$0 \le A_i \le 1,000$ for each valid i$i$
Subtask #2 (70 points): original constraints

-----Example Input-----
1
5 2
1 1 3 3 5

-----Example Output-----
4

-----Explanation-----
Example case 1: The actual sequence of powers is [21,21,23,23,25]=[2,2,8,8,32]$[2^1, 2^1, 2^3, 2^3, 2^5] = [2, 2, 8, 8, 32]$. The maximum product is 20⋅32=640$20 \cdot 32 = 640$. In the optimal solution, the sequence is partitioned into [2,2,8,8]$[2, 2, 8, 8]$ and [32]$[32]$.
-/

def find_optimal_split (N k : Nat) (powers : List Nat) : Nat :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def calc_product (values : List Nat) (split : Nat) : Nat :=
sorry

theorem find_optimal_split_properties1 {N k : Nat} {powers : List Nat} (h1: N ≥ 2) (h2: k ≥ 1) 
    (h3: powers.length = N) (h4: ∀ x ∈ powers, x ≤ 10) :
    let result := find_optimal_split N k powers
    1 ≤ result ∧ result ≤ N-1 :=
sorry

theorem find_optimal_split_properties2 {N k : Nat} {powers : List Nat} (h1: N ≥ 2) (h2: k ≥ 1)
    (h3: powers.length = N) (h4: ∀ x ∈ powers, x ≤ 10) :
    let values := powers.map (fun p => k^p)
    let result := find_optimal_split N k powers
    let optimal_product := calc_product values result
    ∀ i, 1 ≤ i → i < N → calc_product values i ≤ optimal_product :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_optimal_split 5 2 [1, 1, 3, 3, 5]

-- Apps difficulty: interview
-- Assurance level: guarded