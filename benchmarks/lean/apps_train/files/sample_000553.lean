Kefaa has developed a novel decomposition of a tree. He claims that this decomposition solves many difficult problems related to trees. However, he doesn't know how to find it quickly, so he asks you to help him.
You are given a tree with $N$ vertices numbered $1$ through $N$. Let's denote an edge between vertices $u$ and $v$ by $(u, v)$. The triple-tree decomposition is a partition of edges of the tree into unordered triples of edges $(a, b), (a, c), (a, d)$ such that $a \neq b \neq c \neq d$. Each edge must belong to exactly one triple.
Help Kefaa with this problem — find a triple-tree decomposition of the given tree or determine that no such decomposition exists.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- Each of the following $N-1$ lines contains two space-separated integers $u$ and $v$ describing an edge between vertices $u$ and $v$ of the tree.

-----Output-----
- For each test case, print a line containing the string "YES" if a triple-tree decomposition of the given tree exists or "NO" otherwise.
- If it exists, print $\frac{N-1}{3}$ more lines describing a decomposition.
- Each of these lines should contain four space-separated integers $a$, $b$, $c$ and $d$ describing a triple of edges $(a, b), (a, c), (a, d)$.
If more than one triple-tree decomposition exists, you may output any one.

-----Constraints-----
- $1 \le T \le 100$
- $2 \le N \le 2 \cdot 10^5$
- $1 \le u, v \le N$
- the sum of $N$ over all test cases does not exceed $2 \cdot 10^5$

-----Subtasks-----
Subtask #1 (20 points): $2 \le N \le 10$
Subtask #2 (30 points):$2 \le N \le 5000$ and the sum of $N$ overall testcases doesn't exceed $5000$
Subtask #3 (50 points): original constraints

-----Example Input-----
2
4
1 2
1 3
1 4
7
1 2
2 3
1 4
4 5
1 6
6 7

-----Example Output-----
YES
1 2 3 4
NO

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible