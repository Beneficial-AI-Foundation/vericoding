Little X has n distinct integers: p_1, p_2, ..., p_{n}. He wants to divide all of them into two sets A and B. The following two conditions must be satisfied:  If number x belongs to set A, then number a - x must also belong to set A.  If number x belongs to set B, then number b - x must also belong to set B. 

Help Little X divide the numbers into two sets or determine that it's impossible.

-----Input-----

The first line contains three space-separated integers n, a, b (1 ≤ n ≤ 10^5; 1 ≤ a, b ≤ 10^9). The next line contains n space-separated distinct integers p_1, p_2, ..., p_{n} (1 ≤ p_{i} ≤ 10^9).

-----Output-----

If there is a way to divide the numbers into two sets, then print "YES" in the first line. Then print n integers: b_1, b_2, ..., b_{n} (b_{i} equals either 0, or 1), describing the division. If b_{i} equals to 0, then p_{i} belongs to set A, otherwise it belongs to set B.

If it's impossible, print "NO" (without the quotes).

-----Examples-----
Input
4 5 9
2 3 4 5

Output
YES
0 0 1 1

Input
3 3 4
1 2 4

Output
NO

-----Note-----

It's OK if all the numbers are in the same set, and the other one is empty.

def solve_partition (n : Nat) (a b : Int) (xs : List Int) : Option (List Nat) := sorry

def is_valid_partition (n : Nat) (a b : Int) (xs : List Int) (result : Option (List Nat)) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded
