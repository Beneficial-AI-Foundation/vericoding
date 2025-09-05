Chef has $N$ markers. There is a cap on each marker. For each valid $i$, the $i$-th marker has colour $a_i$. Initially, for each valid $i$, the colour of the cap on the $i$-th marker is also $a_i$.
Chef wants to rearrange the caps in such a way that no marker has the same colour as its cap. (Obviously, each marker must have exactly one cap.) Can he do that? If he can, find one such way to rearrange the caps. If there are multiple solutions, you may find any one.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $a_1, a_2, \ldots, a_N$.

-----Output-----
- For each test case:
- If Chef cannot successfully rearrange the caps, print a single line containing the string "No" (without quotes).
- Otherwise, print two lines. The first line should contain the string "Yes" (without quotes). The second line should contain $N$ space-separated integers describing a valid rearrangement of caps. For each valid $i$, the $i$-th of these integers should denote the final colour of the cap on the $i$-th marker.

-----Constraints-----
- $1 \le T \le 10$
- $1 \le N \le 10^5$
- $1 \le a_i \le 10^9$ for each valid $i$

-----Example Input-----
2
9
1 1 1 2 2 2 3 3 3
2
1 1

-----Example Output-----
Yes
2 2 2 3 3 3 1 1 1
No

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
