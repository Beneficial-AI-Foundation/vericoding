Let's denote as $\text{popcount}(x)$ the number of bits set ('1' bits) in the binary representation of the non-negative integer x.

You are given multiple queries consisting of pairs of integers l and r. For each query, find the x, such that l ≤ x ≤ r, and $\text{popcount}(x)$ is maximum possible. If there are multiple such numbers find the smallest of them.

-----Input-----

The first line contains integer n — the number of queries (1 ≤ n ≤ 10000).

Each of the following n lines contain two integers l_{i}, r_{i} — the arguments for the corresponding query (0 ≤ l_{i} ≤ r_{i} ≤ 10^18).

-----Output-----

For each query print the answer in a separate line.

-----Examples-----
Input
3
1 2
2 4
1 10

Output
1
3
7

-----Note-----

The binary representations of numbers from 1 to 10 are listed below:

1_10 = 1_2

2_10 = 10_2

3_10 = 11_2

4_10 = 100_2

5_10 = 101_2

6_10 = 110_2

7_10 = 111_2

8_10 = 1000_2

9_10 = 1001_2

10_10 = 1010_2

def get_max_popcount (l r : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded
