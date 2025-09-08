/-
Corruption is on the rise in the country of Freedonia, Gru's home. Gru wants to end this for good and for that he needs the help of his beloved minions.
This corruption network can be represented in the form of a tree having N$N$ nodes and N−1$N-1$ edges. The nodes are numbered from 1$1$ to N$N$, and the tree is rooted at node 1$1$. These nodes represent the corrupt officials and each corrupt official works under some other corrupt official except the Boss who is represented by node 1$1$.
Gru believes in divide and conquer and thinks that this network needs to be divided into as many sub-networks as possible.
He commands the minions to kill some of the corrupt officials in order to break the network into maximum sub-networks. But as you know, these corrupt officials are very sharp, and hence these assassinations need to be done very smartly and silently, without leaving any traces.  To achieve this Gru devises a strategy, in which he designs an operation, and that operation can be applied by the minions any number of times (even 0). 
In one operation the minions can select any one leaf node official [that is an official who does not have any other official beneath him] in the graph and kill him along with all his ancestors$ancestors$ officials till the root$root$ of the tree in which the operation is applied (this is done to wipe all traces of the operation). This deleted all those nodes from the graph, and also, while doing so, all the associated edges/connections$edges/connections$ of the leaf node and its ancestors are also destroyed. Hence after applying this operation on any tree, it breaks into some connected components which are also trees, which are the new sub-networks.
Now the minions are a bit lazy and will do the task someday, but they need to submit a report to Gru containing the number of the maximum$maximum$ connected$connected$ components$components$ that they could achieve by applying the operation any number of times. To do this, the minions require your help. So help the minions by finding out the maximum$maximum$ no.$no.$ of$of$ connected$connected$ components$components$ that can be achieved.
Note: After each operation, the topmost node (node with the lowest level. It can be proved that there will always be a unique node with the lowest level in each tree) of each of the remaining trees becomes the root of that particular tree (that is, after the first operation it can be visualized that the graph converts into a forest of rooted trees)

-----Input:-----
- First line will contain N$N$, number of nodes in the tree. 
- Next N−1$N-1$ lines contains 2 integers U$U$, V$V$ denoting the endpoints of the ith$i^{th}$ edge.

-----Output:-----
- Print the maximum number of connected components you can obtain after doing the operation any number of times.

-----Constraints-----
- 1≤N≤106$1 \leq N \leq 10^6$
- 1≤U,V≤N$1 \leq U,V \leq N$

-----Sample Input:-----
7
1 2
1 3
2 4
2 5
3 6
3 7

-----Sample Output:-----
2

-----EXPLANATION:-----
We have 4 leaf nodes in this tree: 4 5 6 7. Suppose we delete node 5, then along with it we also delete node 2 and node 1. so after the deletion we are left with 2 trees, one consisting of only node 4 as the root node of that particular tree, and the other consisting of node 3,6,7 with node 3 as the root node. This can also be achieved by deleting any of the other leaf nodes and it can be proved that we cannot obtain more than 2 connected components in this example.
-/

def find_max_components (n: Nat) (edges: List (Nat × Nat)) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def is_tree (n: Nat) (edges: List (Nat × Nat)) : Bool :=
  sorry

theorem line_graph_components {n: Nat} (h: n ≥ 2) :
  let edges := List.range (n-1) |>.map (λi => (i+1, i+2))
  find_max_components n edges = 1 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_max_components 7 [(1, 2), (1, 3), (2, 4), (2, 5), (3, 6), (3, 7)]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_max_components 3 [(1, 2), (2, 3)]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_max_components 4 [(1, 2), (1, 3), (1, 4)]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible