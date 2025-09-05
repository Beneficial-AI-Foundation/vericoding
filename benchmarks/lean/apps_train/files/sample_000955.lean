Given an array $A$ of size $N$ , count number of pairs of index $i,j$ such that $A_i$ is even, $A_j$ is odd and $i < j$

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases.   
- The first line of each test case contains integer $N$.    
- The second line of each test case contains $N$ space separated integers $A_i$. 

-----Output-----
For each test case, print a single line containing an integer denoting number of pairs.

-----Constraints-----
- $1 \le T \le 100$
- $2 \le N \le 10^5$ 
- $1 \le A_i \le 10^9$
- Sum of $N$ over all test cases doesn't exceed $10^6 $ 

-----Subtasks-----
Subtask #1 (30 points):
- $2 \le N \le 100$ 
Subtask #2 (70 points): original constraints

-----Example Input-----
2
4
1 2 1 3
5
5 4 1 2 3

-----Example Output-----
2
3

-----Explanation-----
Example case 1:$(A_2,A_3)$ and $(A_2,A_4)$ . 
Example case 2:$(A_2,A_3)$ , $(A_2,A_5)$ and $(A_4,A_5)$  .

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible