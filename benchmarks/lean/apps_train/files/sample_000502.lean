We have a tree with N vertices, whose i-th edge connects Vertex u_i and Vertex v_i.
Vertex i has an integer a_i written on it.
For every integer k from 1 through N, solve the following problem:
 - We will make a sequence by lining up the integers written on the vertices along the shortest path from Vertex 1 to Vertex k, in the order they appear. Find the length of the longest increasing subsequence of this sequence.
Here, the longest increasing subsequence of a sequence A of length L is the subsequence A_{i_1} , A_{i_2} , ... , A_{i_M} with the greatest possible value of M such that 1 \leq i_1 < i_2 < ... < i_M \leq L and A_{i_1} < A_{i_2} < ... < A_{i_M}.

-----Constraints-----
 - 2 \leq N \leq 2 \times 10^5
 - 1 \leq a_i \leq 10^9
 - 1 \leq u_i , v_i \leq N
 - u_i \neq v_i
 - The given graph is a tree.
 - All values in input are integers.

-----Input-----
Input is given from Standard Input in the following format:
N
a_1 a_2 ... a_N
u_1 v_1
u_2 v_2
:
u_{N-1} v_{N-1}

-----Output-----
Print N lines. The k-th line, print the length of the longest increasing subsequence of the sequence obtained from the shortest path from Vertex 1 to Vertex k.

-----Sample Input-----
10
1 2 5 3 4 6 7 3 2 4
1 2
2 3
3 4
4 5
3 6
6 7
1 8
8 9
9 10

-----Sample Output-----
1
2
3
3
4
4
5
2
2
3

For example, the sequence A obtained from the shortest path from Vertex 1 to Vertex 5 is 1,2,5,3,4. Its longest increasing subsequence is A_1, A_2, A_4, A_5, with the length of 4.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
