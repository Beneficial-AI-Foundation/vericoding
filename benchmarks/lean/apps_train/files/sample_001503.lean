Anas is playing an amazing game on a grid with $N$ rows and $M$ columns. The rows are numbered $1$ through $N$ from top to bottom and the columns are numbered $1$ through $M$ from left to right.
Anas wants to destroy this grid. To do that, he wants to send two heroes from the top left cell to the bottom right cell:
- The first hero visits cells in row-major order: $(1,1) \rightarrow (1,2) \rightarrow \ldots \rightarrow (1,M) \rightarrow (2,1) \rightarrow (2,2) \rightarrow \ldots \rightarrow (2,M) \rightarrow \ldots \rightarrow (N,M)$.
- The second hero visits cells in column-major order: $(1,1) \rightarrow (2,1) \rightarrow \ldots \rightarrow (N,1) \rightarrow (1,2) \rightarrow (2,2) \rightarrow \ldots \rightarrow (N,2) \rightarrow \ldots \rightarrow (N,M)$.
We know that each hero destroys the first cell he visits, rests in the next $K$ cells he visits without destroying them, then destroys the next cell he visits, rests in the next $K$ cells, destroys the next cell, and so on until he reaches (and rests in or destroys) the last cell he visits.
Anas does not know the value of $K$. Therefore, for each value of $K$ between $0$ and $N \cdot M - 1$ inclusive, he wants to calculate the number of cells that will be destroyed by at least one hero. Can you help him?

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains two space-separated integers $N$ and $M$.

-----Output-----
For each test case, print a single line containing $N \cdot M$ space-separated integers as described above.

-----Constraints-----
- $1 \le T \le 100$
- $2 \le N, M \le 1,000$
- the sum of $N \cdot M$ over all test cases does not exceed $2 \cdot 10^6$

-----Subtasks-----
Subtask #1 (30 points):
- $2 \le N, M \le 50$
- the sum of $N \cdot M$ over all test cases does not exceed $5,000$
Subtask #2 (70 points): original constraints

-----Example Input-----
1
2 3

-----Example Output-----
6 4 3 3 2 1

-----Explanation-----
Example case 1:
- $K = 0$: All cells will be destroyed by the heroes.
- $K = 1$: The first hero will destroy the cells $[(1,1), (1,3), (2,2)]$, while the second one will destroy the cells $[(1,1), (1,2), (1,3)]$.
- $K = 2$: The first hero will destroy the cells $[(1,1), (2,1)]$, while the second one will destroy the cells $[(1,1), (2,2)]$.
- $K = 3$: The first hero will destroy the cells $[(1,1), (2,2)]$, while the second one will destroy the cells $[(1,1), (1,3)]$.
- $K = 4$: The first hero will destroy the cells $[(1,1), (2,3)]$ and the second one will also destroy the cells $[(1,1), (2,3)]$.
- $K = 5$ : The first hero will destroy the cell $(1,1)$ and the second one will also destroy the cell $(1,1)$.

def solve (n m : Nat) : List Nat := sorry

def cell_advance_hero1 (row col n m k : Nat) : (Nat × Nat) := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded