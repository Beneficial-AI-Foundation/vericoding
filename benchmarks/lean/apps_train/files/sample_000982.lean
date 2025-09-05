Navnit is a college student and there are $N$ students in his college .Students are numbered from $1$ to $N$.
You are given $M$ facts that "Student $A_i$ and $B_i$".The same fact can be given multiple times .If $A_i$ is a friend of $B_i$ ,then $B_i$ is also a friend of $A_i$ . If $A_i$ is a friend of $B_i$ and $B_i$ is a friend of $C_i$ then $A_i$ is also a friend of $C_i$.
Find number of ways in which two students can be selected in such a way that they are not friends. 

-----Input:-----
- First line will contain two integers $N$ and $M$. 
- Then $M$ lines follow. Each line contains two integers $A_i$ and $B_i$ denoting the students who are friends.

-----Output:-----
For each testcase, output the number of ways in which  two students can be selected in such a way that they are friends.

-----Constraints-----
- $2 \leq N \leq 200000$
- $0 \leq M \leq 200000$
- $1 \leq A_i,B_i \leq N$

-----Sample Input:-----
5 3
1 2                                                   
3 4
1 5

-----Sample Output:-----
6

-----EXPLANATION:-----
Groups of friend are $[1,2,5]$ and $[3,4]$.Hence the answer is  3 X 2 =6.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
