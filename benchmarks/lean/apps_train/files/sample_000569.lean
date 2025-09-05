You are an evil sorcerer at a round table with $N$ sorcerers (including yourself). You can cast $M$ spells which have distinct powers $p_1, p_2, \ldots, p_M$.
You may perform the following operation any number of times (possibly zero):
- Assign a living sorcerer to each positive integer cyclically to your left starting from yourself ― the closest living sorcerer to your left is assigned to $1$, the next living sorcerer to the left is assigned to $2$ and so on. Note that each living sorcerer (including yourself) is assigned to an infinite number of integers.
- Choose a spell $j$ (possibly a spell you have chosen before) and kill the living sorcerer assigned to $p_j$. You may not cast a spell to kill yourself. 

What is the maximum number of sorcerers you can kill using zero or more operations?

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains two space-separated integers $N$ and $M$.
- The second line contains $M$ space-separated integers $p_1, p_2, \ldots, p_M$.

-----Output-----
For each test case, print a single line containing one integer ― the maximum number of sorcerers you can kill.

-----Constraints-----
- $1 \le T \le 1,000$
- $1 \le N \le 10^9$
- $1 \le M \le 3 \cdot 10^5$
- $1 \le p_i \le 10^9$ for each valid $i$
- $p_1, p_2, \ldots, p_N$ are pairwise distinct
- the sum of $M$ over all test cases does not exceed $3 \cdot 10^5$

-----Example Input-----
5
4 1
5
6 2
2 4
1 4
7 16 8 29
1000000000 1
998244353
1 1
20201220

-----Example Output-----
3
4
0
1755647
0

-----Explanation-----
Example case 1: The initial state is shown in the figure from the statement. We can first use spell $1$ and kill the $5$-th sorcerer to our left, i.e. sorcerer $2$. Now there are $3$ living sorcerers and the state is as shown in the following figure:

We can use spell $1$ again and kill the current $5$-th living sorcerer to our left, i.e. sorcerer $4$. Now there are $2$ living sorcerers and the state is:

Finally, we can use spell $1$ again and kill the only other living sorcerer, i.e. sorcerer $3$. Now, none of the other sorcerers are alive. As we cannot cast a spell to kill ourselves, we cannot improve the answer any further.
Example case 2: We can perform $4$ operations using the spell $p_1 = 2$ each time. We can also instead use $p_2 = 4$ in the first two operations and $p_1 = 2$ in the last two operations. Note that there may be multiple valid sequences of operations that lead to the best answer.
Example case 3: We cannot perform any operations using any of the given spells, so we are unable to kill any sorcerers.
Example case 4: We can perform $1,755,647$ operations, each of them using the spell $p_1 = 998,244,353$.

def gcd (a b : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
