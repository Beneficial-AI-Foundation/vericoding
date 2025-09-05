There's a tree and every one of its nodes has a cost associated with it. Some of these nodes are labelled special nodes. You are supposed to answer a few queries on this tree. In each query, a source and destination node (SNODE$SNODE$ and DNODE$DNODE$) is given along with a value W$W$. For a walk between SNODE$SNODE$ and DNODE$DNODE$ to be valid you have to choose a special node and call it the pivot P$P$. Now the path will be SNODE$SNODE$ ->P$ P$ -> DNODE$DNODE$. For any valid path, there is a path value (PV$PV$) attached to it. It is defined as follows:
Select a subset of nodes(can be empty)  in the path from SNODE$SNODE$ to P$P$ (both inclusive) such that sum of their costs (CTOT1$CTOT_{1}$) doesn't exceed W$W$.
Select a subset of nodes(can be empty) in the path from P$P$ to DNODE$DNODE$ (both inclusive) such that sum of their costs (CTOT2$CTOT_{2}$) doesn't exceed W$W$.
Now define PV=CTOT1+CTOT2$PV = CTOT_{1} + CTOT_{2}$ such that the absolute difference  x=|CTOT1−CTOT2|$x = |CTOT_{1} - CTOT_{2}|$ is as low as possible. If there are multiple pairs of subsets that give the same minimum absolute difference, the pair of subsets which maximize PV$PV$ should be chosen.
For each query, output the path value PV$PV$ minimizing x$x$ as defined above. 
Note that the sum of costs of an empty subset is zero.

-----Input-----
- First line contains three integers N$N$ - number of vertices in the tree, NSP$NSP$ - number of special nodes in the tree and Q$Q$ - number of queries to answer.   
- Second line contains N−1$N-1$ integers. If the i$i$th integer is Vi$V_i$ then there is an undirected edge between i+1$i + 1$ and Vi$V_i$ (i$i$ starts from 1$1$ and goes till N−1$N-1$).          
- Third line contains N$N$ integers, the i$i$th integer represents cost of the i$i$th vertex.    
- Fourth line contains NSP$NSP$ integers - these represent which nodes are the special nodes.    
- Following Q$Q$ lines contains three integers each - SNODE$SNODE$, DNODE$DNODE$ and W$W$ for each query.

-----Output-----
For each query output a single line containing a single integer - the path value PV$PV$ between SNODE$SNODE$ and DNODE$DNODE$.

-----Constraints:-----
- 1≤$1 \leq $ Number of nodes ≤1000$ \leq 1000 $ 
- 0≤W≤1000$ 0 \leq W \leq 1000 $ 
- 1≤$ 1 \leq $ Number of special nodes ≤10$ \leq 10 $ 
- 0≤$ 0 \leq $ Cost of each node ≤1000$ \leq 1000 $ 
- 1≤$ 1 \leq $ Number of queries ≤1000$ \leq 1000 $

-----Sample Input-----
7 1 5

1 1 2 2 3 3

3 5 4 2 7 9 1

1

2 3 100

1 1 100

2 1 100

4 5 100

4 7 100      

-----Sample Output:-----
6

6

6

20

16       

-----Explanation:-----
Consider query 4$4$. The only path is 4−>2−>1−>2−>5$4->2->1->2->5$. The two sets defined for this path are {3,2,5${3,2,5}$} and {3,5,7${3,5,7}$}. Pick subsets {3,2,5${3,2,5}$} and {3,7${3,7}$} from each set which minimizes PV$PV$. Note that node 2$2$ can repeat as it is in different paths (both to and from the pivot).

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded