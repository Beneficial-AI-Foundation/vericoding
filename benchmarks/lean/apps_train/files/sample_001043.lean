You are given an unweighted tree with N$N$ nodes (numbered 1$1$ through N$N$). Let's denote the distance between any two nodes p$p$ and q$q$ by d(p,q)$d(p, q)$.
You should answer Q$Q$ queries. In each query, you are given parameters a$a$, da$d_a$, b$b$, db$d_b$, and you should find a node x$x$ such that d(x,a)=da$d(x, a) = d_a$ and d(x,b)=db$d(x, b) = d_b$, or determine that there is no such node.

-----Input-----
- The first line of the input contains a single integer T$T$ denoting the number of test cases. The description of T$T$ test cases follows.
- The first line of each test case contains two space-separated integers N$N$ and Q$Q$.
- Each of the next N−1$N-1$ lines contains two space-separated integers u$u$ and v$v$ denoting that nodes u$u$ and v$v$ are connected by an edge.
- Each of the next Q$Q$ lines contains four space-separated integers a$a$, da$d_a$, b$b$ and db$d_b$ describing a query.

-----Output-----
For each query, print a single line containing one integer ― the number of a node satisfying the given requirements, or −1$-1$ if no such node exists.
If there are multiple solutions, you may output any one.

-----Constraints-----
- 1≤T≤1,000$1 \le T \le 1,000$
- 1≤N,Q≤106$1 \le N, Q \le 10^6$
- 1≤u,v≤N$1 \le u, v \le N$
- the graph on the input is a tree
- 1≤a,b≤N$1 \le a, b \le N$
- 1≤da,db<N$1 \le d_a, d_b < N$
- the sum of N$N$ over all test cases does not exceed 106$10^6$
- the sum of Q$Q$ over all test cases does not exceed 106$10^6$

-----Subtasks-----
Subtask #1 (50 points):
- 1≤N,Q≤1,000$1 \le N, Q \le 1,000$
- the sum of N$N$ over all test cases does not exceed 1,000$1,000$
- the sum of Q$Q$ over all test cases does not exceed 1,000$1,000$
Subtask #2 (50 points): original constraints

-----Example Input-----
1
5 3
1 2
2 3
3 4
3 5
2 1 4 1
2 2 4 2
1 1 2 1

-----Example Output-----
3
5
-1

def find_nodes_with_distance (t : Tree) (node : Nat) (dist : Nat) : List Nat :=
  sorry

def resolve_query (t : Tree) (a b c d : Nat) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded