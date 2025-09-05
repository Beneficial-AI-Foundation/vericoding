Increasing COVID cases have created panic amongst the people of Chefland, so the government is starting to push for production of a vaccine. It has to report to the media about the exact date when vaccines will be available.
There are two companies which are producing vaccines for COVID. Company A starts producing vaccines on day $D_1$ and it can produce $V_1$ vaccines per day. Company B starts producing vaccines on day $D_2$ and it can produce $V_2$ vaccines per day. Currently, we are on day $1$.
We need a total of $P$ vaccines. How many days are required to produce enough vaccines? Formally, find the smallest integer $d$ such that we have enough vaccines at the end of the day $d$.

-----Input-----
- The first and only line of the input contains five space-separated integers $D_1$, $V_1$, $D_2$, $V_2$ and $P$.

-----Output-----
Print a single line containing one integer ― the smallest required number of days.

-----Constraints-----
- $1 \le D_1, V_1, D_2, V_2 \le 100$
- $1 \le P \le 1,000$

-----Subtasks-----
Subtask #1 (30 points): $D_1 = D_2$
Subtask #2 (70 points): original constraints

-----Example Input 1-----
1 2 1 3 14

-----Example Output 1-----
3

-----Explanation-----
Since $D_1 = D_2 = 1$, we can produce $V_1 + V_2 = 5$ vaccines per day. In $3$ days, we produce $15$ vaccines, which satisfies our requirement of $14$ vaccines.

-----Example Input 2-----
5 4 2 10 100

-----Example Output 2-----
9

-----Explanation-----
There are $0$ vaccines produced on the first day, $10$ vaccines produced on each of days $2$, $3$ and $4$, and $14$ vaccines produced on the fifth and each subsequent day. In $9$ days, it makes a total of $0 + 10 \cdot 3 + 14 \cdot 5 = 100$ vaccines.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
