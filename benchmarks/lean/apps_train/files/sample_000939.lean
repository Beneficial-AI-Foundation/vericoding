You are given a rooted tree on N vertices. The nodes are numbered from 1 to N, and Node 1 is the root. Each node u has an associated value attached to it: Au.
For each vertex v, we consider the path going upwards from v to the root. Suppose that path is v1, v2, .., vk, where v1 = v and vk = 1. The cost of any node on this path is equal to the minimum value among all the nodes to its left in the path sequence, including itself. That is, cost(vi) = min1 <= j <= i{Avj}. And the cost of the path is the sum of costs of all the nodes in it.
For every node in the tree, find the cost of the path from that node to the root.

-----Input-----
- The first line of the input contains a single integer, N, denoting the number of nodes in the tree.
- The next line contains N-1 integers, the i-th of which denotes the parent of node i+1.
- The next line contains N integers, the i-th of which denotes Ai.

-----Output-----
Output a single line containing N integers, the i-th of which should be the cost of the path from node i to the root.

-----Constraints-----
- 1 ≤ N ≤ 100,000
- -1,000,000,000 ≤ Av ≤ 1,000,000,000

-----Subtasks-----
- Subtask #1 (30 points): 1 ≤ N ≤ 2000
- Subtask #2 (70 points): Original constraints.

-----Example-----
Input:
8
1 1 1 1 5 8 6
1 2 3 4 5 15 70 10

Output: 
1 3 4 5 6 21 96 26

-----Explanation-----
For example, take a look at the path from vertex 7: The path is 7 -> 8 -> 6 -> 5 -> 1.
Cost(7) has no choice but to be A7. So Cost(7) = 70.
Cost(8) will be minimum of A7 and A8, which turns out to be A8. So Cost(8) = 10.
Cost(6) = minimum {A7, A8, A6} = minimum {70, 10, 15} = 10.
Cost(5) = minimum {70, 10, 15, 5} = 5.
Cost(1) = minimum {70, 10, 15, 5, 1} = 1. 
So, the cost of the path from 7 to the root is 70 + 10 + 10 + 5 + 1 = 96.

def calculate_path_costs (n: Nat) (parents: List Nat) (values: List Nat) : List Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
