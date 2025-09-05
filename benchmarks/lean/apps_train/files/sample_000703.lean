The kingdom of the snakes is an NxN grid. Their most-valued possession is a huge collection of poison, which is stored in the central KxK grid. It is guaranteed that both N and K are odd. What we mean by 'central' is this: suppose in the NxN grid, (i, j) refers to the cell in the i-th row and j-th column and (1,1) refers to the top-left corner and (N,N) refers to the bottom-right corner. Then the poison is stored in the KxK square whose top-left corner is ( (N - K)/2 + 1, (N - K)/2 + 1 ).

But there are thieves who want to steal the poison. They cannot enter the NxN grid, but they can shoot arrows from outside. These arrows travel across a row (from left to right, or right to left), or across a column (top to bottom or bottom to top) in a straight line. If the arrow enters the KxK grid, some of the poison will stick to the arrow, and if it exits the NxN grid after that, the thieves will have successfully stolen some of the poison.
As the King of the snakes, you want to thwart these attempts. You know that the arrows will break and stop if they hit a snake's scaly skin, but won't hurt the snakes. There are some snakes already guarding the poison. Each snake occupies some consecutive cells in a straight line inside the NxN grid. That is, they are either part of a row, or part of a column. Note that there can be intersections between the snakes.  A configuration of snakes is 'safe', if the thieves cannot steal poison. That is, no matter which row or column they shoot arrows from, either the arrow should hit a snake and stop (this can happen even after it has entered and exited the KxK grid), or it shouldn't ever enter the KxK grid.
The King has other duties for the snakes, and hence wants to remove as many snakes as possible from this configuration, such that the remaining configuration is still 'safe'. Help him find the minimum number of snakes he needs to leave behind to protect the poison.

-----Input-----
- The first line contains a single integer, T, the number of testcases.
- The first line of each testcase contains three integers: N, K and M, where N is the size of the entire square grid, K is the size of the square containing the poison, and M is the number of initial snakes.
- M lines follow, the i-th of which contains four integers: HXi, HYi, TXi, TYi. (HXi, HYi) is the cell which contains the head of the i-th snake. (TXi, TYi) is the cell which contains the tail of the i-th snake. It is guaranteed that both these cells will either lie in the same row, or same column. And hence the cells in between them, including these two cells, represents the i-th snake.

-----Output-----
- For each testcase, output a single integer in a new line: The minimum number of the snakes that the king can keep and still protect the poison. If it is not possible to protect the poison even with all the snakes, output -1.

-----Constraints-----
- 1 ≤ T ≤ 4
- 3 ≤ N ≤ 109
- 1 ≤ K ≤ N-2
- Both N and K will be odd integers
- 1 ≤ M ≤ 105
- 1 ≤ HXi, HYi, TXi, TYi ≤ N
- It is guaranteed that at least one of (HXi = TXi), and (HYi = TYi) will be true for all i
- None of the cells in the KxK grid will be occupied by any snake

-----Example-----
Input:
2
7 3 7
1 1 6 1
1 2 3 2
5 2 5 2
2 4 2 6
6 2 6 4
5 6 5 7
7 1 7 4
7 3 7
1 1 6 1
1 2 3 2
5 2 5 2
2 6 2 6
6 2 6 4
5 6 5 7
7 1 7 4

Output:
3
-1

-----Explanation-----
The first example corresponds to:

Note that the top-left corner cell of the NxN grid is by definition, (1,1). The inner square contains the poison, and the seven snakes are shown in different colours. The green snake is the 1st snake in the input.
We can remove all but 3 snakes and protect the poison. One such configuration is this:

You can check that no arrow can enter the inner poison square and exit the outer square without hitting a snake. Hence is it safe. Also, you cannot do this with fewer snakes. Hence 3 is the answer.
The second testcase corresponds to:

You can check that even with all the snakes, this is not a safe configuration, because the thieves can shoot an arrow down the 5th column, and they can steal poison. Hence, the answer is -1.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded