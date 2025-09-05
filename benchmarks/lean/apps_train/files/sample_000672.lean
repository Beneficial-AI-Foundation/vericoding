You are given a sequence $A_1, A_2, \ldots, A_N$. For each valid $i$, the star value of the element $A_i$ is the number of valid indices $j < i$ such that $A_j$ is divisible by $A_i$.
Chef is a curious person, so he wants to know the maximum star value in the given sequence. Help him find it.

-----Input-----
- The first line of the input contains a single integer $T$ which denotes the number of test cases.
- The first line of each test case contains a single integer $N$ .
- The second line of each test case contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output-----
For each test case, print a single line containing one integer ― the maximum star value.

-----Constraints-----
- $1 \le T \le 10$
- $1 \le N \le 10^5$
- $1 \le A_i \le 10^6$ for each valid $i$ 
- Sum of $N$ over all test cases does not exceed $100,000$.

-----Subtasks-----
Subtask #1 (20 points): sum  of $N$ over all test cases does not exceed $5,000$
Subtask #2 (80 points): original constraints

-----Example Input-----
1
7
8 1 28 4 2 6 7

-----Example Output-----
3

-----Explanation-----
$A_5 = 2$ divides $4$, $28$ and $8$, so its star value is $3$. There is no element with a higher star value.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
