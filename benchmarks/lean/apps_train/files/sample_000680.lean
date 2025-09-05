Chef wants to host some Division-3 contests. Chef has $N$ setters who are busy creating new problems for him. The $i^{th}$ setter has made $A_i$ problems where $1 \leq i \leq N$.    
A Division-3 contest should have exactly $K$ problems. Chef wants to plan for the next $D$ days using the problems that they have currently. But Chef cannot host more than one Division-3 contest in a day.
Given these constraints, can you help Chef find the maximum number of Division-3 contests that can be hosted in these $D$ days?

-----Input:-----
- The first line of input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains three space-separated integers - $N$, $K$ and $D$ respectively.
- The second line of each test case contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$ respectively. 

-----Output:-----
For each test case, print a single line containing one integer ― the maximum number of Division-3 contests Chef can host in these $D$ days.

-----Constraints-----
- $1 \leq T \leq 10^3$
- $1 \leq N \leq 10^2$
- $1 \le K \le 10^9$ 
- $1 \le D \le 10^9$
- $1 \le A_i \le 10^7$ for each valid $i$

-----Subtasks-----
Subtask #1 (40 points):
- $N = 1$
- $1 \le A_1 \le 10^5$
Subtask #2 (60 points): Original constraints

-----Sample Input:-----
5
1 5 31
4
1 10 3
23
2 5 7
20 36
2 5 10
19 2
3 3 300
1 1 1

-----Sample Output:-----
0
2
7
4
1

-----Explanation:-----
- 
Example case 1: Chef only has $A_1 = 4$ problems and he needs $K = 5$ problems for a Division-3 contest. So Chef won't be able to host any Division-3 contest in these 31 days. Hence the first output is $0$.
- 
Example case 2: Chef has $A_1 = 23$ problems and he needs $K = 10$ problems for a Division-3 contest. Chef can choose any $10+10 = 20$ problems and host $2$ Division-3 contests in these 3 days. Hence the second output is $2$.
- 
Example case 3: Chef has $A_1 = 20$ problems from setter-1 and $A_2 = 36$ problems from setter-2, and so has a total of $56$ problems. Chef needs $K = 5$ problems for each Division-3 contest. Hence Chef can prepare $11$ Division-3 contests. But since we are planning only for the next $D = 7$ days and Chef cannot host more than $1$ contest in a day, Chef cannot host more than $7$ contests. Hence the third output is $7$.

def List.sum : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + sum xs

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
