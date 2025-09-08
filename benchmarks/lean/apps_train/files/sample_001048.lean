/-
$Jaggu$ monkey a friend of $Choota$ $Bheem$ a great warrior of $Dholakpur$. He gets everything he wants. Being a friend of $Choota$ $Bheem$ he never has to struggle for anything, because of this he is in a great debt of $Choota$ $Bheem$, he really wants to pay his debt off.
Finally the time has come to pay his debt off, $Jaggu$ is on a magical tree. He wants to collect apples from different branches but he is in a hurry. $Botakpur$ has attacked on $Dholakpur$ and $Bheem$ is severely injured, as been instructed by the village witch, $Bheem$ can only be saved by the apples of the magical tree. Each apple is placed in Tree Node structure and each apple has some sweetness. Now there's a problem as $Jaggu$ is also injured so he can only slide downwards and alse is collecting apples in his hand so he can't climb. You would be given $Q$ queries. Queries are of 2 type :-
- 
Ending Node Node of $Jaggu$ is given. $format$ - type of query node -(1 2)
- 
Sweetness of Apple on a given node is changed. $format$ - type of query node new sweetness(2 3 10)
$Note$: $Jaggu$ is always on the top of tree initially in each query.The sweetness is always positive.
Help $Jaggu$ in saving $Bheem$

-----Input:-----
- First line contains $N$ - (number of nodes).  
- Next line contains $N$ integers with space giving sweetness of apple on Nodes $(1 to N)$
- Next $N-1$ lines contain  $N1$ $N2$ connected nodes.
- Next line contains single integer $Q$ Number of queries

-----Output:-----
- For each query of type 1, print total sweetness of apples. 

-----Constraints-----
- $1 \leq N \leq 10^4$
- $2 \leq Q \leq 10^4$

-----Sample Input:-----
10
10 12 6 8 1 19 0 5 13 17
1 2
1 3
1 4
3 10
4 8
8 9
4 5
5 7
5 6
3
1 1
2 3 20
1 8

-----Sample Output:-----
10
23

-----EXPLANATION:-----
This sweetness array is :
$[10,2,6,8,1,19,0,5,13,17]$
The tree is:
1   

/  |   \      

2    3     4     

/    /    \      

10     8        5   

/        /    \     

9         7        6
-/

def solve_tree_queries (n : Nat) (sweetness : List Int) (edges : List (Nat × Nat))
  (queries : List QueryType) : List Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def is_tree (n : Nat) (edges : List (Nat × Nat)) : Bool :=
  sorry

theorem solve_tree_queries_outputs_len {n : Nat} {sweetness : List Int} 
  {edges : List (Nat × Nat)} {queries : List QueryType}
  (h1 : sweetness.length = n)
  (h2 : is_tree n edges = true) :
  (solve_tree_queries n sweetness edges queries).length = 
  (queries.filter (fun q => match q with 
                           | QueryType.get _ => true
                           | _ => false)).length :=
sorry 

theorem solve_tree_queries_outputs_integers {n : Nat} {sweetness : List Int}
  {edges : List (Nat × Nat)} {queries : List QueryType} 
  {result : List Int}
  (h1 : sweetness.length = n)
  (h2 : is_tree n edges = true)
  (h3 : result = solve_tree_queries n sweetness edges queries) :
  ∀ x, x ∈ result → x ∈ sweetness ∨ ∃ q, q ∈ queries ∧ (
    match q with
    | QueryType.update _ v => v = x
    | _ => False
  ) :=
sorry

theorem solve_tree_queries_idempotent {n : Nat} {sweetness : List Int}
  {edges : List (Nat × Nat)} {val : Int} {node : Nat}
  (h1 : sweetness.length = n)
  (h2 : is_tree n edges = true)
  (h3 : node ≤ n) :
  (solve_tree_queries n sweetness edges 
    [QueryType.update node val, QueryType.get node]).length = 1 :=
sorry

-- Apps difficulty: interview
-- Assurance level: guarded