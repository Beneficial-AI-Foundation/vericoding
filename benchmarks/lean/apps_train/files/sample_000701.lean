All strings in Chefland are beautiful because they are binary strings (a binary string contains only characters '0' and '1'). The beauty of a binary string $S$ is defined as the number of pairs $(i, j)$ ($1 \le i \le j \le |S|$) such that the substring $S_i, S_{i+1}, \ldots, S_j$ is special.
For a binary string $U$, let's denote the number of occurrences of the characters '1' and '0' in $U$ by $cnt_1$ and $cnt_0$ respectively; then, $U$ is special if $cnt_0 = cnt_1 \cdot cnt_1$.
Today, Chef's friend Araspa is celebrating her birthday. Chef wants to give Araspa the most beautiful binary string he can find. Currently, he is checking out binary strings in a shop, but he needs your help to calculate their beauties. Tell Chef the beauty of each binary string he gives you.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains a single string $S$.

-----Output-----
For each test case, print a single line containing one integer — the beauty of the string $S$.

-----Constraints-----
- $1 \le T \le 10$
- $1 \le |S| \le 10^5$
- each character of $S$ is '0' or '1'

-----Example Input-----
2
010001
10

-----Example Output-----
4
1

-----Explanation-----
Example case 1: The special substrings correspond to $(i, j) = (1, 2), (1, 6), (2, 3), (5, 6)$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible