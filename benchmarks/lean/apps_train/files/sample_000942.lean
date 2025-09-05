You are given a sequence $A_1, A_2, \ldots, A_N$. You want all the elements of the sequence to be equal. In order to achieve that, you may perform zero or more moves. In each move, you must choose an index $i$ ($1 \le i \le N$), then choose $j = i-1$ or $j = i+1$ (it is not allowed to choose $j = 0$ or $j = N+1$) and change the value of $A_i$ to $A_j$ — in other words, you should replace the value of one element of the sequence by one of its adjacent elements.
What is the minimum number of moves you need to make in order to make all the elements of the sequence equal?

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output-----
For each test case, print a single line containing one integer — the minimum required number of moves.

-----Constraints-----
- $1 \le T \le 100$
- $1 \le N \le 100$
- $1 \le A_i \le 100$ for each valid $i$

-----Example Input-----
3
5
1 1 1 1 1
4
9 8 1 8
2
1 9

-----Example Output-----
0
2
1

-----Explanation-----
Example case 1: No moves are needed since all the elements are already equal.
Example case 3: We can perform one move on either $A_1$ or $A_2$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible