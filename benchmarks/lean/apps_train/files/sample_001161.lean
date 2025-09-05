Kim has broken in to the base, but after walking in circles, perplexed by the unintelligible base design of the JSA, he has found himself in a large, empty, and pure white, room. 
The room is a grid with H∗W$H*W$ cells, divided into H$H$ rows and W$W$ columns. The cell (i,j)$(i,j)$ is at height A[i][j]$A[i][j]$. Unfortunately, his advanced sense of smell has allowed him to sense a mercury leak, probably brought in by Jishnu to end his meddling. The mercury leak has a power (which determines what height the mercury can reach before dissipating into harmless quantities) and a source cell. It spreads from cells it has already reached to other cells in the four cardinal directions: north, south, east, and west. (That is, the mercury can spread up, down, right, or left in the grid, but not diagonally.) Mercury can only spread to a cell if the cell's height is strictly less than the power value. 
Unfortunately, Kim does not exactly know the starting cell or the power value of the mercury leak. However, his impressive brain has determined that it must be one of Q$Q$ (power, starting cell) combinations. For each combination, he wants to find out how many cells are dangerous for him to go to: that is, how many cells will eventually be reached by the mercury. This will help him determine a suitable cell to stay in and slowly fix the leak from above.
Can you help Kim achieve this objective?
Note: If the starting cell's height is not less than the power level, the mercury immediately dissipates. So, in this case, output 0.

-----Input:-----
- First line will contain T$T$, number of testcases. Then the testcases follow. 
- The first line in each testcase contains three integers, H$H$, W$W$, and Q$Q$.
- On the 2$2$nd to (H+1)$(H+1)$th lines of each testcase: The (i+1)$(i+1)$th line contains W$W$ space-separated integers, representing the heights of the cells on the i$i$th row of the grid.
- On the (H+2)$(H+2)$th to (H+Q+1)$(H+Q+1)$th lines of each testcase: The (i+H+1)$(i+H+1)$th line contains 3 space-separated integers, r[i]$r[i]$, c[i]$c[i]$, and p[i]$p[i]$, which represents a (power, starting cell) combination. For this specific combination, the mercury leak originates on the cell (r[i],c[i])$(r[i],c[i])$ and has power p[i]$p[i]$.

-----Output:-----
For each testcase, output Q$Q$ lines, with each line containing one integer. The i$i$th line should output the number of dangerous cells, given that the leak originated on cell (r[i],c[i])$(r[i],c[i])$ with power p[i]$p[i]$, as defined in the input. Read the sample and sample explanation for more details.

-----Constraints-----
- 1≤T≤2$1 \leq T \leq 2$ 
- 1≤H≤1000$1 \leq H \leq 1000$
- 1≤W≤1000$1 \leq W \leq 1000$
- 1≤Q≤2∗105$1 \leq Q \leq 2*10^5$
- 1≤r[i]≤H$1 \leq r[i] \leq H$ for all i$i$
- 1≤c[i]≤W$1 \leq c[i] \leq W$ for all i$i$
- 0≤A[i][j]≤109$0 \leq A[i][j] \leq 10^9$ for all (i,j)$(i,j)$
- 0≤p[i]≤109$0 \leq p[i] \leq 10^9$ for all i$i$.

-----Subtasks-----
- 10 points : A[i][j]=$A[i][j] =$ constant k$k$ for all (i,j)$(i,j)$ (the heights of all cells are equal).   
- 20 points : H=1$H=1$, Q≤1000$Q \leq 1000$.   
- 30 points: r[i]=$r[i] =$ constant x$x$, c[i]=$c[i] =$ constant y$y$ for all i$i$ (the starting cell is fixed).   
- 40 points: No additional constraints.   

-----Sample Input:-----
1
5 5 3
4 3 9 7 2
8 6 5 2 8
1 7 3 4 3
2 2 4 5 6
9 9 9 9 9
3 4 6
3 2 5
1 4 9

-----Sample Output:-----
10
0
19

-----EXPLANATION:-----
For the first query, the cell (3,4)$(3,4)$ has height 4. The mercury can reach the following cells: (2,3)$(2,3)$, (2,4)$(2,4)$, (3,1)$(3,1)$, (3,3)$(3,3)$, (3,4)$(3,4)$, (3,5)$(3,5)$, (4,1)$(4,1)$, (4,2)$(4,2)$, (4,3)$(4,3)$, (4,4)$(4,4)$, for a total of 10. Note that it cannot reach cell (4,5)$(4,5)$ because the height (6) is equal to the power value (6).
For the second query, the cell (3,2)$(3,2)$ has height 7. Since the power value of 5 is less than or equal to the height of 7, the mercury immediately dissipates and so it reaches 0 cells.
For the third query, the mercury can reach all cells except the bottom row and the cell (1,3)$(1,3)$.
Note that (x,y)$(x,y)$ means the cell on the x$x$-th row and y$y$-th column.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded