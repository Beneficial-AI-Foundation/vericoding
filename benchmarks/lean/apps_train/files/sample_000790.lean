Chef is frustrated in this lockown. So to overcome this he plans to travel various mountains.
He is very strange so he sets some conditions for $each$ Type 2 query(mentioned below) (i.e. $1$ $i$) : 
- Let Chef has travelled till $ith$ mountain from left to right.
- He does not like to travel the mountain with the height ,of which he has travelled till now. More formally, 
Let the height of peak on which he is standing is $a_{i}$ then he can only go to the peak of height $a_{j}$ 
which is greater than $a_{i}$ and nearest to $ith$ mountain such that there should be no other peak of same height $a_{j}$ till $a_{i}$(height of $ith$ mountain) .

-----Input format:-----
- 
The first line contains an integer $T$ denoting the number of test cases.
- 
The second line of  consist of a integer $N$ and $Q$ .
- 
The third line contains $N$ not necessarily distinct positive integers $a_{0},a_{1}, . . .,a_{n-1}$ denoting the height of 
$N$ mountains.
- 
Then next $Q$ lines follows where each line consisting of $either$ of $2$ types of queries:
Type 1:  $0$ $A$ $B$ i.e. $a_{A} = B$ (where height of $Ath$ mountain will be updated to $B$) 
Type 2:  $1$ $A$ i.e. you have to answer $a_k$ which is greater than $a_{A}$ and nearest to $Ath$ mountain such that there should be no other peak of same height $a_{k}$ till $a_{A}$(height of $Ath$ mountain) .

-----Output format:-----
- For every query of Type 2 there should be an integer $a_{k}$ on next  line for the updated array , If no such $a_{k}$ exists then $a_{k}$= $-1$ , as query of type 1 will have no output . 

-----Constraints:-----
- $1\leq T \leq 10^2$
- $1 \leq N,Q \leq 10^4$
- $0\leq a_{i} \leq 10^6$
- $0\leq B \leq 10^6$
- $0\leq A \leq N-1$

-----Subtasks-----
- 
1 Point :   
$1 \leq T,N,Q \leq 10^2$ 
$0\leq B,a_{i} \leq 10^2$
- 
99 Points : Orginal   Constraints

-----Example:-----

-----Input:-----
1
10 5
1 3 5 4 5 6 7 8  4 5
1 7
1 3
1 1
0 2 7
1 3

-----Output:-----
-1
6
5
5

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded