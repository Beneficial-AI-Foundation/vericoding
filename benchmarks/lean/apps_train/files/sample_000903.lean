You are given a tree with $N$ vertices (numbered $1$ through $N$) and a bag with $N$ markers. There is an integer written on each marker; each of these integers is $0$, $1$ or $2$. You must assign exactly one marker to each vertex.
Let's define the unattractiveness of the resulting tree as the maximum absolute difference of integers written on the markers in any two vertices which are connected by an edge.
Find the minimum possible unattractiveness of the resulting tree.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers denoting the numbers on markers in the bag.
- Each of the next $N-1$ lines contains two space-separated integers $u$ and $v$ denoting an edge between vertices $u$ and $v$.

-----Output-----
For each test case, print a single line containing one integer — the minimum unattractiveness.

-----Constraints-----
- $1 \le T \le 30$
- $1 \le N \le 100$
- $1 \le u, v \le N$
- the graph described on the input is a tree

-----Example Input-----
3
3
0 1 1
1 2
1 3
3
0 1 2
1 2
1 3
4
2 2 2 2
1 2
1 3
3 4

-----Example Output-----
1
1
0

-----Explanation-----
Example case 1:

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
