/-
Given an undirected tree consisting of n vertices numbered from 1 to n. A frog starts jumping from the vertex 1. In one second, the frog jumps from its current vertex to another unvisited vertex if they are directly connected. The frog can not jump back to a visited vertex. In case the frog can jump to several vertices it jumps randomly to one of them with the same probability, otherwise, when the frog can not jump to any unvisited vertex it jumps forever on the same vertex. 
The edges of the undirected tree are given in the array edges, where edges[i] = [fromi, toi] means that exists an edge connecting directly the vertices fromi and toi.
Return the probability that after t seconds the frog is on the vertex target.

Example 1:

Input: n = 7, edges = [[1,2],[1,3],[1,7],[2,4],[2,6],[3,5]], t = 2, target = 4
Output: 0.16666666666666666 
Explanation: The figure above shows the given graph. The frog starts at vertex 1, jumping with 1/3 probability to the vertex 2 after second 1 and then jumping with 1/2 probability to vertex 4 after second 2. Thus the probability for the frog is on the vertex 4 after 2 seconds is 1/3 * 1/2 = 1/6 = 0.16666666666666666. 

Example 2:

Input: n = 7, edges = [[1,2],[1,3],[1,7],[2,4],[2,6],[3,5]], t = 1, target = 7
Output: 0.3333333333333333
Explanation: The figure above shows the given graph. The frog starts at vertex 1, jumping with 1/3 = 0.3333333333333333 probability to the vertex 7 after second 1. 

Example 3:
Input: n = 7, edges = [[1,2],[1,3],[1,7],[2,4],[2,6],[3,5]], t = 20, target = 6
Output: 0.16666666666666666

Constraints:

1 <= n <= 100
edges.length == n-1
edges[i].length == 2
1 <= edges[i][0], edges[i][1] <= n
1 <= t <= 50
1 <= target <= n
Answers within 10^-5 of the actual value will be accepted as correct.
-/

def isValidTree (n : Nat) (edges : List (List Nat)) : Bool :=
sorry

/- Function that computes probability of frog being at target vertex after t steps -/

-- <vc-helpers>
-- </vc-helpers>

def frogPosition (n : Nat) (edges : List (List Nat)) (t : Nat) (target : Nat) : Float :=
sorry

theorem frog_position_probability (n : Nat) (edges : List (List Nat)) 
    (t : Nat) (target : Nat) 
    (h : isValidTree n edges = true) :
  let prob := frogPosition n edges t target
  0 ≤ prob ∧ prob ≤ 1 ∧ 1 ≤ target ∧ target ≤ n :=
sorry

theorem frog_position_deterministic (n : Nat) (edges : List (List Nat))
    (t : Nat) (target : Nat) 
    (h : isValidTree n edges = true) :
  let prob1 := frogPosition n edges t target
  let prob2 := frogPosition n edges t target
  prob1 = prob2 := 
sorry

theorem frog_position_impossible_start (n : Nat) (edges : List (List Nat))
    (target : Nat)
    (h1 : isValidTree n edges = true)
    (h2 : target ≠ 1) :
  frogPosition n edges 0 target = 0 :=
sorry

-- Apps difficulty: interview
-- Assurance level: guarded