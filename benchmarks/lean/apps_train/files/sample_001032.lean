Chefland is a grid with N$N$ rows and M$M$ columns. Each cell of this grid is either empty or contains a house. The distance between a pair of houses is the Manhattan distance between the cells containing them.
For each d$d$ between 1$1$ and N+M−2$N+M-2$ inclusive, Chef wants to calculate the number of unordered pairs of distinct houses with distance equal to d$d$. Please help him!

-----Input-----
- The first line of the input contains a single integer T$T$ denoting the number of test cases. The description of T$T$ test cases follows.
- The first line of each test case contains two space-separated integers N$N$ and M$M$.
- N$N$ lines follow. For each i$i$ (1≤i≤N$1 \le i \le N$), the i$i$-th of these lines contains a binary string with length M$M$; for each j$j$ (1≤j≤M$1 \le j \le M$), the j$j$-th character of this string is '1' if the cell in the i$i$-th row and j$j$-th column contains a house or '0' if it is empty.

-----Output-----
For each test case, print a single line containing N+M−2$N+M-2$ space-separated integers. For each valid i$i$, the i$i$-th integer should denote the number of pairs with distance i$i$.

-----Constraints-----
- 1≤T≤3$1 \le T \le 3$
- 2≤N,M≤300$2 \le N, M \le 300$

-----Subtasks-----
Subtask #1 (50 points): N,M≤50$N, M \le 50$
Subtask #2 (50 points): original constraints

-----Example Input-----
1
3 4
0011
0000
0100

-----Example Output-----
1 0 1 1 0

def make_grid (n m : Nat) (house_coords : List (Nat × Nat)) : List String := sorry

def solve_house_distances (n m : Nat) (grid : List String) : List Nat := sorry

def sum_list : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + sum_list xs

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded