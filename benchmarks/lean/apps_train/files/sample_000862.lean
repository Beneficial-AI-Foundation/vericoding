Arya and Aryan live in a country called Nadaca. Nadaca consists of $N$ cities numbered $1$ through $N$, which are connected by some bidirectional roads. Each road has a positive (not necessarily integer) length. Arya lives in city $1$ and Aryan lives in city $N$.
Arya claims that for each city $v$, the shortest path from city $1$ to city $v$ has length $a_v$. Aryan does not disagree, but claims that for each city $v$, the shortest path from city $N$ to city $v$ has length $b_v$. You are the wisest person they know, so they asked you to tell them if it is possible for their claims to be true, i.e. if a road network which fully satisfies their claims exists. Help them!

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $a_1, a_2, \ldots, a_N$.
- The third line contains $N$ space-separated integers $b_1, b_2, \ldots, b_N$.

-----Output-----
For each test case, print a single line containing the string "Yes" if Arya's and Aryan's claims can be true or "No" otherwise.

-----Constraints-----
- $1 \le T \le 10^3$
- $2 \le N \le 10^6$
- $0 \le a_i, b_i \le 10^9$ for each valid $i$
- the sum of $N$ over all test cases does not exceed $10^6$

-----Subtasks-----
Subtask #1 (50 points): the sum of $N$ over all test cases does not exceed $10^3$
Subtask #2 (50 points): original constraints

-----Example Input-----
2
3
0 1 1
1 1 0
3
0 1 5
5 1 0

-----Example Output-----
Yes
No

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded