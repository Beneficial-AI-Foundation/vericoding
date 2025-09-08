/-
A "graph" consists of "nodes", also known as "vertices". Nodes may or may not be connected with one another. 
In our definition below the node "A0" is connected with the node "A3", but "A0" is not connected with "A1".

The connecting line between two nodes is called an edge. If the edges between the nodes are undirected, 
the graph is called an undirected graph. A weighted graph is a graph in which a number (the weight) is assigned to each edge.
A graph is acyclic if it has no loop.

A graph can be represented as a dictionary:

`graph = {'A0': [('A3', 1), ('A5', 4)], 
 'A1': [('A2', 2)], 
 'A2': [('A1', 1), ('A2', 2), ('A3', 1), ('A4', 1)],
 'A3': [('A0', 1), ('A2', 1)], 
 'A4': [('A2', 1), ('A4', 1)], 
 'A5': [('A3', 3)]
}`

Here the nodes are A0...A5; following each nodes is the edges list of linked nodes with their weight.
A0 is linked to A3 with a weight of 1 and to A5 with weight 4. A dictionary is not ordered but the list
of linked nodes is sorted. So: 

`'A0': [('A3', 1), ('A5', 4)]`is correct but `'A0': [('A5', 4), ('A3', 1)]`is not.

The edges E of a graph G induce a binary relation that is called the adjacency relation of G.
One can associate an adjacency matrix:

`M = 
[[0, 0, 0, 1, 0, 4], 
 [0, 0, 2, 0, 0, 0], 
 [0, 1, 2, 1, 1, 0], 
 [1, 0, 1, 0, 0, 0], 
 [0, 0, 1, 0, 1, 0], 
 [0, 0, 0, 3, 0, 0]]`

Let us imagine that lines are numbered from A0 to A5 and the same for columns.
The first line correspond to A0 and we can see that A0 is connected to A3 with weight 1, A0 is also connected to A5 with weight 4.

Another way is to use an adjacency list: An adjacency list representation for a graph 
associates each vertex in the graph with the collection of its neighboring edges:

`L = [['A0', [('A3', 1), ('A5', 4)]], 
     ['A1', [('A2', 2)]], 
     ['A2', [('A1', 1), ('A2', 2), ('A3', 1), ('A4', 1)]], 
     ['A3', [('A0', 1), ('A2', 1)]], 
     ['A4', [('A2', 1), ('A4', 1)]], 
     ['A5', [('A3', 3)]]] `

L is sorted in order A0 to A5 and each sublist is sorted as in a graph dictionary.

In the kata nodes will be numbered from A0 to A(n-1) for a graph with n nodes. 
The task is to go from each represention to each other one
and at last to find *all* paths from a node to another node.

Below is a skeleton for our class `Graph`.

class Graph():

    def __init__(self, vertices_num):
        # number of nodes (an integer)
        self.v = vertices_num
        # (maybe not useful here) : list of nodes from "A0", "A1" ... to "A index (vertices_num - 1)"
        self.nodes = None

    # from adjacency matrix to dictionary
    def adjmat_2_graph(self, adjm):

    # from dictionary to adjacency matrix
    def graph_2_mat(self, graph):

    # from dictionary to adjacency list    
    def graph_2_list(self, graph):

    # from adjacency list to dictionary
    def list_2_graph(self, lst):

    # from adjacency matrix to adjacency list    
    def mat_2_list(self, mat):

    # from adjacency list to adjacency matrix
    def list_2_mat(self, lst):

    # find all paths from node start_vertex to node end_vertex
    def find_all_paths(self, graph, start_vertex, end_vertex):

# Examples: 
- see: graph, M, L above.
- finding all paths:

`dct = {'A3': [('A0', 1), ('A2', 1)], 'A0': [('A3', 1), ('A2', 1)], 'A4': [('A2', 1)], 'A1': [('A2', 1)], 'A2': [('A1', 1), ('A2', 1), ('A3', 1), ('A4', 1)]}`

`g = Graph(5)`

`g.find_all_paths(dct, "A0", "A4") return l = ['A0-A2-A4', 'A0-A3-A2-A4']`

Note that ['A0-A2-A4', 'A0-A3-A2-A4'] is sorted (hint: sorted(sorted(l, key=str), key=len))

Translators and critics are welcome.
-/

def Graph.adjmat_2_graph {n : Nat} (g : Graph n) (mat : List (List Nat)) : List (String × List (String × Nat)) := sorry 
def Graph.graph_2_list {n : Nat} (g : Graph n) (graph : List (String × List (String × Nat))) : List (Nat × Nat × Nat) := sorry

-- <vc-helpers>
-- </vc-helpers>

def Graph.list_2_graph {n : Nat} (g : Graph n) (lst : List (Nat × Nat × Nat)) : List (String × List (String × Nat)) := sorry

theorem graph_initialization (size : Nat) (h : size > 0) : 
  ∃ g : Graph size, true 
  := sorry

theorem adjmat_graph_properties {size : Nat} (h : size > 0) (mat : List (List Nat)) :
  ∀ g : Graph size,
  let graph := Graph.adjmat_2_graph g mat
  (∀ k ∈ graph, String.startsWith (k.fst) "A") ∧ 
  graph.length = size
  := sorry

theorem list_conversion_properties {size : Nat} (h : size > 0) (graph : List (String × List (String × Nat))) :
  ∀ g : Graph size,
  let lst := Graph.graph_2_list g graph
  let result := Graph.list_2_graph g lst
  (∀ k ∈ result, String.startsWith (k.fst) "A") ∧ 
  (∀ v ∈ result, v.snd.all (λ x => true))
  := sorry

-- Apps difficulty: interview
-- Assurance level: unguarded