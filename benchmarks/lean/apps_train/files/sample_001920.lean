Toad Rash has a binary string $s$. A binary string consists only of zeros and ones.

Let $n$ be the length of $s$.

Rash needs to find the number of such pairs of integers $l$, $r$ that $1 \leq l \leq r \leq n$ and there is at least one pair of integers $x$, $k$ such that $1 \leq x, k \leq n$, $l \leq x < x + 2k \leq r$, and $s_x = s_{x+k} = s_{x+2k}$.

Find this number of pairs for Rash.

-----Input-----

The first line contains the string $s$ ($1 \leq |s| \leq 300\,000$), consisting of zeros and ones.

-----Output-----

Output one integer: the number of such pairs of integers $l$, $r$ that $1 \leq l \leq r \leq n$ and there is at least one pair of integers $x$, $k$ such that $1 \leq x, k \leq n$, $l \leq x < x + 2k \leq r$, and $s_x = s_{x+k} = s_{x+2k}$.

-----Examples-----
Input
010101

Output
3

Input
11001100

Output
0

-----Note-----

In the first example, there are three $l$, $r$ pairs we need to count: $1$, $6$; $2$, $6$; and $1$, $5$.

In the second example, there are no values $x$, $k$ for the initial string, so the answer is $0$.

def count_valid_pairs (s : String) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible