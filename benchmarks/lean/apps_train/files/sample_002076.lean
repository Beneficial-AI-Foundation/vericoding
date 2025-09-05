Iahub is very proud of his recent discovery, propagating trees. Right now, he invented a new tree, called xor-tree. After this new revolutionary discovery, he invented a game for kids which uses xor-trees.

The game is played on a tree having n nodes, numbered from 1 to n. Each node i has an initial value init_{i}, which is either 0 or 1. The root of the tree is node 1.

One can perform several (possibly, zero) operations on the tree during the game. The only available type of operation is to pick a node x. Right after someone has picked node x, the value of node x flips, the values of sons of x remain the same, the values of sons of sons of x flips, the values of sons of sons of sons of x remain the same and so on.

The goal of the game is to get each node i to have value goal_{i}, which can also be only 0 or 1. You need to reach the goal of the game by using minimum number of operations.

-----Input-----

The first line contains an integer n (1 ≤ n ≤ 10^5). Each of the next n - 1 lines contains two integers u_{i} and v_{i} (1 ≤ u_{i}, v_{i} ≤ n; u_{i} ≠ v_{i}) meaning there is an edge between nodes u_{i} and v_{i}. 

The next line contains n integer numbers, the i-th of them corresponds to init_{i} (init_{i} is either 0 or 1). The following line also contains n integer numbers, the i-th number corresponds to goal_{i} (goal_{i} is either 0 or 1).

-----Output-----

In the first line output an integer number cnt, representing the minimal number of operations you perform. Each of the next cnt lines should contain an integer x_{i}, representing that you pick a node x_{i}.

-----Examples-----
Input
10
2 1
3 1
4 2
5 1
6 2
7 5
8 6
9 8
10 5
1 0 1 1 0 1 0 1 0 1
1 0 1 0 0 1 1 1 0 1

Output
2
4
7

def solve_xor_tree (n : Nat) (edges : List (Nat × Nat)) (init : List Nat) (goal : List Nat) : List Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded