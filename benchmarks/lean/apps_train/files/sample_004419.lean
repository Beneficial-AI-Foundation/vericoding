In graph theory, a graph is a collection of nodes with connections between them.
Any node can be connected to any other node exactly once, and can be connected to no nodes, to some nodes, or to every other node.
Nodes cannot be connected to themselves
A path through a graph is a sequence of nodes, with every node connected to the node following and preceding it.
A closed path is a path which starts and ends at the same node.

An open path:
```
1 -> 2 -> 3
```
a closed path:
```
1 -> 2 -> 3 -> 1
```
A graph is connected if there is a path from every node to every other node.
A graph is a tree if it is connected and there are no closed paths.

Your job is to write a function 'isTree', which returns true if a graph is a tree, and false if it is not a tree.

Graphs will be given as an array with each item being an array of integers which are the nodes that node is connected to.

For example, this graph:
```
0--1
|  |
2--3--4
```
has array:
```
[[1,2], [0,3], [0,3], [1,2,4], [3]]
```
Note that it is also not a tree, because it contains closed path:
```
0->1->3->2->0
```
A node with no connections is an empty array
Note that if node 0 is connected to node 1, node 1 is also connected to node 0. This will always be true.
The order in which each connection is listed for each node also does not matter.

Good luck!

def isTree (graph : List (List Nat)) : Bool := sorry 

def isValidAdjacencyMatrix (matrix : List (List Nat)) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
