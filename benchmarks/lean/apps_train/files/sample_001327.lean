/-
Salmon loves to be a tidy person. One day, when he looked at the mess that he made after playing with his rubber ducks, he felt awful. Now he wants to clean up his mess, by placing his ducks into boxes.
Each rubber duck has a color. There are a total of $N+1$ colors, numbered from $0$ to $N$. Salmon wants to place his $N*K$ ducks into $N$ boxes, each of which can fit $K$ ducks. Each duck should be placed inside a box.
Salmon is very particular when it comes to how many colors he can place in each box. Since Salmon doesn't like lots of colors mixing together he only wants to have a maximum of $2$ distinct colors per box.
Please help Salmon achieve this goal!

It can be shown that there will always be at least one valid solution under given constraints.

If there are multiple correct solutions, you may output any one of them.   

-----Input:-----
- The first line contains an integer $T$, denoting the number of testcases. $T$ testcases will follow, each containing two lines.   
- The first line of each testcase contains two space-separated integers $N$ and $K$.   
- The second line of each testcase contains $N+1$  space-separated integers. The $i+1$-th integer denotes the number of ducks with color-$i$ where $0 \leq i \leq N$

-----Output:-----
- Output $N$ lines for each testcase. 
- The $i$-th line of a testcase should contain $4$ space-separated integers $c1, m1, c2, m2$ respectively which denotes that that are $m1$ ducks of color-$c1$ and $m2$ ducks of color-$c2$ inside the $i$-th box where $0 \leq m1,m2 \leq K$ and $0 \leq c1,c2 \leq N$. 
- Note that even if you have only one color to put inside the $i$-th box, you should still output $4$ space-separated integers and keep either $m1$ or $m2$ as $0$. And $0 \leq c1,c2 \leq N$.
- The output should be valid and should satisfy Salmon's goal.

-----Constraints-----
- $T=10$
- $2 \leq N \leq 10^5$ 
- $2 \leq K \leq 10^5$ 
- Total ducks for each test case is exactly $N*K$
- There can be a color with $0$ ducks

-----Subtasks-----
- Subtask 1 [20 points]: $2 \leq N \leq 10$, $K=2$ 
- Subtask 2 [30 points]: $N=2$, $K=5$
- Subtask 3 [50 points]: original constraints

-----Sample Input:-----
1
2 4
3 4 1

-----Sample Output:-----
2 1 1 3
1 1 0 3

-----Explanation:-----
- In the given testcase, Salmon has $N=2$ boxes, each of size $K=4$ and there are total $N*K=8$ ducks.   
- The first box is filled with $1$ duck of color-$2$ and $3$ ducks of color-$1$ and the second box is filled with $1$ duck of color-$1$ and $3$ ducks of color-$0$.   
- Each duck is inside a box and each box has at most two distinct colors. Also each box contains exactly $K=4$ ducks.
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_duck_boxes (N K : Nat) (colors : List Nat) : List Box := sorry

def validate_solution (N K : Nat) (colors : List Nat) (result : List Box) : Prop := sorry

-- Main correctness theorems

theorem box_count_correct (N K : Nat) (colors : List Nat) :
  (List.length colors = N + 1) →
  (List.foldr (· + ·) 0 colors ≥ N * K) →
  List.length (solve_duck_boxes N K colors) = N := sorry

theorem box_content_valid (N K : Nat) (colors : List Nat) (box : Box) :
  (List.length colors = N + 1) →
  (List.foldr (· + ·) 0 colors ≥ N * K) →
  box ∈ solve_duck_boxes N K colors →
  box.count1 + box.count2 = K := sorry

theorem box_colors_distinct (N K : Nat) (colors : List Nat) (box : Box) :
  (List.length colors = N + 1) →
  (List.foldr (· + ·) 0 colors ≥ N * K) →
  box ∈ solve_duck_boxes N K colors →
  box.color1 ≠ box.color2 := sorry

theorem box_colors_valid_range (N K : Nat) (colors : List Nat) (box : Box) :
  (List.length colors = N + 1) →
  (List.foldr (· + ·) 0 colors ≥ N * K) →
  box ∈ solve_duck_boxes N K colors →
  box.color1 ≤ N ∧ box.color2 ≤ N := sorry

theorem color_usage_within_limits (N K : Nat) (colors : List Nat) (i : Nat) :
  (List.length colors = N + 1) →
  (List.foldr (· + ·) 0 colors ≥ N * K) →
  i ≤ N →
  (List.foldl (fun acc box => acc + 
    (if box.color1 = i then box.count1 else 0) +
    (if box.color2 = i then box.count2 else 0)
  ) 0 (solve_duck_boxes N K colors)) ≤ List.get! colors i := sorry

-- Minimal input theorem

theorem minimal_input_valid (N K : Nat) :
  N > 0 →
  K > 0 →
  let colors := N*K :: List.replicate N 0
  validate_solution N K colors (solve_duck_boxes N K colors) := sorry

/-
info: N2
-/
-- #guard_msgs in
-- #eval len solve_duck_boxes(N2, K2, colors2)

-- Apps difficulty: interview
-- Assurance level: unguarded