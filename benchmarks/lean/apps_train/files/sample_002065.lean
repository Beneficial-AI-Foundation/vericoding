Consider a sequence [a_1, a_2, ... , a_{n}]. Define its prefix product sequence $[ a_{1} \operatorname{mod} n,(a_{1} a_{2}) \operatorname{mod} n, \cdots,(a_{1} a_{2} \cdots a_{n}) \operatorname{mod} n ]$.

Now given n, find a permutation of [1, 2, ..., n], such that its prefix product sequence is a permutation of [0, 1, ..., n - 1].

-----Input-----

The only input line contains an integer n (1 ≤ n ≤ 10^5).

-----Output-----

In the first output line, print "YES" if such sequence exists, or print "NO" if no such sequence exists.

If any solution exists, you should output n more lines. i-th line contains only an integer a_{i}. The elements of the sequence should be different positive integers no larger than n.

If there are multiple solutions, you are allowed to print any of them.

-----Examples-----
Input
7

Output
YES
1
4
3
6
5
2
7

Input
6

Output
NO

-----Note-----

For the second sample, there are no valid sequences.

def find_permutation_with_prefix_products (n : Nat) : List Nat := sorry

def is_prime (n : Nat) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded