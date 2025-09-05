Chef works in a similar way to a travelling salesman ― he always travels to new cities in order to sell his delicious dishes.
Today, Chef is planning to visit $N$ cities (numbered $1$ through $N$). There is a direct way to travel between each pair of cities. Each city has a specific temperature; let's denote the temperature in the $i$-th city by $C_i$. Chef has a fixed temperature tolerance $D$ with the following meaning: for each pair of cities $a$ and $b$, he may travel from city $a$ directly to city $b$ only if $|C_a-C_b| \le D$, otherwise he would catch a heavy flu because of the sudden change in temperature.
Chef starts from city $1$. Is he able to visit all $N$ cities in such a way that each city is visited exactly once?
Notes:
- Chef is not able to travel through a city without visiting it.
- City $1$ is visited at the beginning.
- It is not necessary to be able to travel directly to city $1$ from the last city Chef visits.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains two space-separated integers $N$ and $D$.
- The second line contains $N$ space-separated integers $C_1, C_2, \ldots, C_N$.

-----Output-----
For each test case, print a single line containing the string "YES" (without quotes) if Chef can visit all cities or "NO" (without quotes) if he cannot.

-----Constraints-----
- $1 \le T \le 1,000$
- $2 \le N \le 10^5$
- $0 \le D \le 10^9$
- $0 \le C_i \le 10^9$ for each valid $i$
- the sum of $N$ over all test cases does not exceed $10^6$

-----Subtasks-----
Subtask #1 (20 points):
- $N \le 1,000$
- the sum of $N$ over all test cases does not exceed $10,000$
Subtask #2 (80 points): original constraints

-----Example Input-----
2
5 3
3 2 1 4 5
5 4
10 1 3 2 9

-----Example Output-----
YES
NO

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded