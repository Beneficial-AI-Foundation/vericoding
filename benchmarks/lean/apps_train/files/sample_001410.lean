Consider the fraction, $a/b$, where $a$ and $b$ are positive integers. If $a < b$ and $GCD(a,b) = 1$, it is called a reduced proper fraction.
If we list the set of a reduced proper fraction for $d \leq 8$, (where $d$ is the denominator) in ascending order of size, we get:
$1/8$, $1/7$, $1/6$, $1/5$, $1/4$, $2/7$, $1/3$, $3/8$, $2/5$ , $3/7$, $1/2$, $4/7$, $3/5$, $5/8$, $2/3$, $5/7$, $3/4$, $4/5$,  $5/6$, $6/7$, $7/8$
It can be seen that $2/5$ is the fraction immediately to the left of $3/7$.
By listing the set of reduced proper fractions for $d \leq N$ in ascending order of value, find the numerator and denominator of the fraction immediately to the left of $a/b$ when $a$ and $b$ are given.

-----Input:-----
- First line of input contains an integer $T$, number of test cases
- Next $T$ lines contain $a$ $b$ $N$ separated by space

-----Output:-----
Print the numerator and denominator separated by a space corresponding to each test case on a new line

-----Constraints-----
- $1 \leq T \leq 50$
- $1 \leq a < b \leq 10^9$
- $GCD(a,b) = 1$
- $b < N \leq 10^{15}$

-----Subtasks-----
- 10 points: $1 \leq N \leq 100$
- 30 points : $1 \leq N \leq 10^6$
- 60 points : $1 \leq N \leq 10^{15}$

-----Sample Input:-----
5
3 7 8
3 5 8
4 5 8
6 7 8
1 5 8

-----Sample Output:-----
2 5
4 7
3 4
5 6
1 6

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
