You have a tree consisting of n vertices. You want to color each vertex of the tree in one of the k colors such that for any pair of vertices having same color, all the vertices belonging to the path joining them should also have same color. In other words, for any two vertices u, v with same color, all the vertices in the path joining them should also have color same as that of the u (or same as v, as u and v have same color). 

Find out possible number of ways in which you can color the tree satisfying the above property. As the answer could be large, print your answer modulo 109 + 7.

-----Input-----
The first line of the input contains an integer T denoting the number of test cases. The description of T test cases follows.
For each test case, first line contains two space separated integers n, k denoting number of vertices in the tree and total number of colors, respectively
Each of the next n - 1 lines contain two space separated integers ui, vi, denoting that there is an edge between vertices ui and vi in the tree.

-----Output-----
For each test case, output a single line corresponding to number of ways of coloring the tree.

-----Constraints-----
- 1 ≤ T ≤ 50
- 1 ≤ n, k ≤ 50
- 1 ≤ ui, vi ≤ n
- ui ≠ vi

-----Example-----
Input
3
3 2
1 2
2 3
3 1
1 2
2 3
4 3
1 2
2 3
2 4

Output:
6
1
39

-----Explanation-----
In the first example, You can color the vertices in the following 6 ways - {1, 1, 1}, {2, 2, 2}, {1, 2, 2}, {1, 1, 2}, {2, 1, 1}, {2, 2, 1}. Note that you can't color the tree in {1, 2, 1} as the vertices in the path connecting vertex 1 and 3, (i.e. 1, 2, 3) don't have same color. You can see that the color of 2nd vertex is not same as that of 1st and 3rd.
In the second example, Only possible coloring you can do is to color all the vertices with color 1.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
