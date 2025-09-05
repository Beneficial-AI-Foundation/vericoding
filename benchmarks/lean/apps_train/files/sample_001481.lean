Istiak is learning about arithmetic progressions. Today, he wrote an arithmetic sequence on a piece of paper. Istiak was very happy that he managed to write an arithmetic sequence and went out for lunch.
Istiak's friend Rafsan likes to irritate him by playing silly pranks on him. This time, he could have chosen one element of Istiak's sequence and changed it. When Istiak came back, he was devastated to see his sequence ruined — it became a sequence $a_1, a_2, \ldots, a_N$ (possibly identical to the original sequence, if Rafsan did not change anything, in which case Istiak is just overreacting). Help him recover the original sequence.
Formally, you have to find an arithmetic sequence $b_1, b_2, \ldots, b_N$ which differs from $a$ in at most one position. $b$ is said to be an arithmetic sequence if there is a real number $d$ such that $b_i - b_{i-1} = d$ for each $i$ ($2 \le i \le N$). If there are multiple valid solutions, you may find any one.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $a_1, a_2, \ldots, a_N$.

-----Output-----
For each test case, print a single line containing $N$ space-separated integers $b_1, b_2, \ldots, b_N$. It is guaranteed that a valid solution exists.

-----Constraints-----
- $4 \le N \le 10^5$
- $|a_i| \le 10^9$ for each valid $i$
- the sum of $N$ over all test cases does not exceed $5 \cdot 10^5$

-----Example Input-----
3
4
1 3 10 7
5
-10 -5 0 5 10
4
2 2 2 10

-----Example Output-----
1 3 5 7
-10 -5 0 5 10
2 2 2 2

-----Explanation-----
Example case 1: Rafsan changed the third element from $5$ to $10$.
Example case 2: No elements were changed.
Example case 3: Rafsan changed the fourth element from $2$ to $10$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
