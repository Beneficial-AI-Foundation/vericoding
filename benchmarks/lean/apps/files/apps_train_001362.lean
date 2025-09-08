/-
You are given a 1×1×2$1 \times 1 \times 2$ bar (a cuboid) and a grid A$A$ with N$N$ rows (numbered 1$1$ through N$N$) and M$M$ columns (numbered 1$1$ through M$M$). Let's denote the cell in row r$r$ and column c$c$ by (r,c)$(r, c)$. Some cells of the grid are blocked, the remaining cells are free.
Each cell has dimensions 1×1$1 \times 1$, the same as two opposite faces of the cuboid. When the bar is placed on the grid in such a way that one of its two 1×1$1 \times 1$ faces fully covers a cell (r,c)$(r, c)$, we say that the bar is standing on the cell (r,c)$(r, c)$. Initially, the bar is standing on a cell (x,y)$(x, y)$.
When the bar is placed on the grid, one of its faces is touching the grid; this face is called the base. In one move, you must roll the bar over one of its base edges (sides of the base); this base edge does not move and the bar is rotated 90∘$90^\circ$ around it in such a way that it is still lying on the grid, but with a different base. In different moves, the bar may be rotated around different edges in different directions. After each move, the base of the bar must lie fully inside the grid and it must not cover any blocked cells.
An example sequence of moves is shown here.
For each cell of the grid, determine the minimum number of moves necessary to achieve the state where the bar is standing on this cell or determine that it is impossible to achieve.

-----Input-----
- The first line of the input contains a single integer T$T$ denoting the number of test cases. The description of T$T$ test cases follows.
- The first line of each test case contains two space-separated integers N$N$ and M$M$.
- The second line contains two space-separated integers x$x$ and y$y$.
- N$N$ lines follow. For each i$i$ (1≤i≤N$1 \le i \le N$), the i$i$-th of these lines contains M$M$ integers Ai,1,Ai,2,…,Ai,M$A_{i, 1}, A_{i, 2}, \ldots, A_{i, M}$ (a string with length M$M$). For each valid i,j$i, j$, Ai,j=0$A_{i, j} = 0$ denotes that the cell (i,j)$(i, j)$ is blocked and Ai,j=1$A_{i, j} = 1$ denotes that it is free.

-----Output-----
For each test case, print N$N$ lines, each containing M$M$ space-separated integers. For each valid i,j$i, j$, the j$j$-th integer on the i$i$-th of these lines should denote the minimum number of moves necessary to have the bar stand on cell (i,j)$(i, j)$, or it should be −1$-1$ if it is impossible.

-----Constraints-----
- 1≤T≤50$1 \le T \le 50$
- 1≤N,M≤1,000$1 \le N, M \le 1,000$
- 1≤x≤N$1 \le x \le N$
- 1≤y≤M$1 \le y \le M$
- 0≤Ai,j≤1$0 \le A_{i, j} \le 1$ for each valid i,j$i, j$
- Ax,y=1$A_{x, y} = 1$
- the sum of N⋅M$N \cdot M$ over all test cases does not exceed 106$10^6$

-----Subtasks-----
Subtask #1 (15 points):
- x=1$x = 1$
- y=1$y = 1$
- Ai,j=1$A_{i, j} = 1$ for each valid i,j$i, j$
Subtask #2 (85 points): original constraints

-----Example Input-----
2
2 4
1 1
1111
0111
2 4
1 1
1111
0011

-----Example Output-----
0 -1 -1 2
-1 -1 -1 3
0 -1 -1 2
-1 -1 -1 -1

-----Explanation-----
Example case 1: Initially, the base of the bar occupies the cell (1,1)$(1, 1)$. After the first move, it occupies the cells (1,2)$(1, 2)$ and (1,3)$(1, 3)$. After the second move, it can occupy the cell (1,4)$(1, 4)$.
Alternatively, after the second move, it can occupy the cells (2,2)$(2, 2)$ and (2,3)$(2, 3)$, and after the third move, it can occupy the cell (2,4)$(2, 4)$.
-/

-- <vc-helpers>
-- </vc-helpers>

def Grid := List (List Int)

def solve_bar_grid (n m x y : Nat) (grid : Grid) : Grid :=
  sorry

theorem grid_dimensions (n m x y : Nat) (grid : Grid) 
  (h1 : 1 ≤ n ∧ n ≤ 10)
  (h2 : 1 ≤ m ∧ m ≤ 10) 
  (h3 : 1 ≤ x ∧ x ≤ n)
  (h4 : 1 ≤ y ∧ y ≤ m) :
  let result := solve_bar_grid n m x y grid
  List.length result = n ∧ 
  List.all result (fun row => List.length row = m) ∧
  List.get! (List.get! result (x-1)) (y-1) = 0 :=
  sorry

theorem isolated_start (n m x y : Nat) (grid : Grid)
  (h1 : 2 ≤ n ∧ n ≤ 5)
  (h2 : 2 ≤ m ∧ m ≤ 5)
  (h3 : 1 ≤ x ∧ x ≤ n)
  (h4 : 1 ≤ y ∧ y ≤ m) :
  let result := solve_bar_grid n m x y grid
  (List.foldl (fun acc row => 
    acc + List.foldl (fun acc' val => if val ≠ -1 then acc' + 1 else acc') 0 row
  ) 0 result) = 1 ∧
  List.get! (List.get! result (x-1)) (y-1) = 0 :=
  sorry

theorem cost_increases :
  let grid : Grid := [[1,1,1], [1,1,1], [1,1,1]]
  let result := solve_bar_grid 3 3 1 1 grid
  ∀ i j, i < 3 → j < 3 →
    let val := List.get! (List.get! result i) j
    (val ≠ -1 ∧ (i,j) ≠ (0,0)) → val > 0 :=
  sorry

-- Apps difficulty: interview
-- Assurance level: guarded