Vision has finally made it to Wakanda to get his MindStone extracted. The MindStone was linked to his brain in a highly sophisticated manner and Shuri had to solve a complex problem to extract the stone. The MindStone had $n$ integers inscribed in it and Shuri needs to apply the prefix sum operation on the array $k$ times to extract the stone.
Formally, given $n$ integers $A[1], A[2] ..... A[n]$ and a number $k$, apply the operation
$A[i] = \sum_{j=1}^{i} A[j]$
on the array $k$ times.
Finally Shuri needs to apply $modulo$ $(10^9 + 7)$ operation to each element of the array. Can you help Shuri accomplish this task before Thanos gets to them?

-----Input:-----
- First line of the input consists of two space separated integers $n$ and $k$. 
- Second line contains $n$ space separated integers $A[1] .. A[n]$.

-----Output:-----
In a single line print $n$ space separated integers, the values of the resultant array after applying all the operations.

-----Constraints-----
- $1 \leq n \leq 1000$
- $1 \leq k \leq 10^{12}$
- $1 \leq A[i] \leq 10^9$

-----Subtasks-----
- 20 Points: $1 \leq k \leq 1000$
- 30 Points: $1 \leq k \leq 1000000$
- 50 Points: Original Constraints

-----Sample Input:-----
$4$ $2$
$3$ $4$ $1$ $5$

-----Sample Output:-----
$3$ $10$ $18$ $31$

-----EXPLANATION:-----
After applying the prefix sum operation once the array becomes -> $3$ $7$ $8$ $13$
After applying the prefix sum operation for the second time, the array becomes -> $3$ $10$ $18$ $31$
After applying $modulo$ $(10^9 +7)$ operation, array becomes -> $3$ $10$ $18$ $31$

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
