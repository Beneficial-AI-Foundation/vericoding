You are given an empty grid with $N$ rows (numbered $1$ through $N$) and $M$ columns (numbered $1$ through $M$). You should fill this grid with integers in a way that satisfies the following rules:
- For any three cells $c_1$, $c_2$ and $c_3$ such that $c_1$ shares a side with $c_2$ and another side with $c_3$, the integers written in cells $c_2$ and $c_3$ are distinct.
- Let's denote the number of different integers in the grid by $K$; then, each of these integers should lie between $1$ and $K$ inclusive.
- $K$ should be minimum possible.
Find the minimum value of $K$ and a resulting (filled) grid. If there are multiple solutions, you may find any one.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains two space-separated integers $N$ and $M$.

-----Output-----
- For each test case, print $N+1$ lines.
- The first line should contain a single integer — the minimum $K$.
- Each of the following $N$ lines should contain $M$ space-separated integers between $1$ and $K$ inclusive. For each valid $i, j$, the $j$-th integer on the $i$-th line should denote the number in the $i$-th row and $j$-th column of the grid.

-----Constraints-----
- $1 \le T \le 500$
- $1 \le N, M \le 50$
- the sum of $N \cdot M$ over all test cases does not exceed $7 \cdot 10^5$

-----Subtasks-----
Subtask #1 (100 points): original constraints

-----Example Input-----
2
1 1
2 3

-----Example Output-----
1
1
3
1 1 2
2 3 3

-----Explanation-----
Example case 1: There is only one cell in the grid, so the only valid way to fill it is to write $1$ in this cell. Note that we cannot use any other integer than $1$.
Example case 2: For example, the integers written in the neighbours of cell $(2, 2)$ are $1$, $2$ and $3$; all these numbers are pairwise distinct and the integer written inside the cell $(2, 2)$ does not matter. Note that there are pairs of neighbouring cells with the same integer written in them, but this is OK.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded