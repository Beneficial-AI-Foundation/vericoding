Chef has  $N$ boxes arranged in a line.Each box has some candies in it,say $C[i]$. Chef wants to distribute all the candies between of his friends: $A$ and $B$, in the following way:
$A$ starts eating candies kept in the leftmost box(box at $1$st place) and $B$ starts eating candies kept in the rightmost box(box at $N$th place). $A$ eats  candies $X$ times faster than $B$ i.e. $A$ eats $X$ candies when $B$ eats only $1$. Candies in each box can be eaten by only the person who reaches that box first. If both reach a box at the same time, then the one who has eaten from more number of BOXES till now will eat the candies in that box. If both have eaten from the same number of boxes till now ,then $A$ will eat the candies in that box.
Find the number of boxes finished by both $A$ and $B$.
NOTE:- We assume that it does not take any time to switch from one box to another.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains three lines of input.
The first line of each test case contains $N$, the number of boxes.
- The second line of each test case contains a sequence,$C_1$ ,$C_2$ ,$C_3$ . . . $C_N$ where $C_i$ denotes the number of candies in the i-th box.  
- The third line of each test case contains an integer $X$ .

-----Output:-----
For each testcase, print two space separated integers in a new line - the number of boxes eaten by $A$  and  $B$ respectively. 

-----Constraints-----
- $1 \leq T \leq 100$
- $1 \leq N \leq 200000$
- $1 \leq C_i \leq 1000000$
- $1 \leq X \leq 10$
- Sum of $N$ over all test cases does not exceed $300000$

-----Subtasks-----
Subtask 1(24 points):
- $1 \leq T \leq 10$
- $1 \leq N \leq 1000$
- $1 \leq C_i \leq 1000$
- $1 \leq X \leq 10$
Subtask 2(51 points): original constraints

-----Sample Input:-----
1
5
2 8 8 2 9
2

-----Sample Output:-----
4 1

-----EXPLANATION:-----
$A$ will start eating candies in the 1st box(leftmost box having 2 candies) . $B$ will start eating candies in the  5th box(rightmost box having 9 candies) .As $A's$ speed is 2 times as that of $B's$, $A$ will start eating candies in the  2nd box while $B$ would still be eating candies in the 5th box.$A$ will now start eating candies from the 3rd box while $B$ would still be eating candies in the 5th box.Now both $A$ and $B$ will finish candies in their respective boxes at the same time($A$ from the 3rd box and $B$ from 5th box). Since $A$ has eaten more number of boxes($A$ has eaten 3 boxes while $B$ has eaten 1 box) till now,so $A$ will be eating candies in the 4th box.
Hence $A$ has eaten 4 boxes and $B$ has eaten 1 box.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
