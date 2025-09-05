-----Problem Statement-----
We have an integer sequence $A$, whose length is $N$.
Find the number of the non-empty contiguous subsequences of $A$ whose sum is $0$. Note that we are counting the ways to take out subsequences. That is, even if the contents of some two subsequences are the same, they are counted individually if they are taken from different positions.

-----Input-----
Input is given in the following format:
$N$
$A_1$ $A_2$  . . .  $A_N$

-----Output-----
Find the number of the non-empty contiguous subsequences of $A$ whose sum is $0$.

-----Constraints-----
- $1 \leq N \leq 2\times10^5$
- $-10^9 \leq A_i \leq 10^9$
- All values in input are integers.

-----Sample Input-----
6
1 3 -4 2 2 -2

-----Sample Output-----
3

-----EXPLANATION-----
There are three contiguous subsequences whose sums are $0$: $(1, 3, -4)$, $(-4, 2, 2)$ and $(2, -2)$

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded