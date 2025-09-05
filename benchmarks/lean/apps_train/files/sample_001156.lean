Every college has a stud−max$stud-max$ buoy. JGEC$JGEC$ has its own Atul$Atul$ who loves to impress everyone with his smile. A presentation is going on at the auditorium where there are N$N$ rows of M$M$ chairs with people sitting on it. Everyone votes for Atul's presentation skills, but Atul is interested in knowing the maximum$maximum$ amount of vote that he receives either taking K$K$ people vertically$vertically$ or horizontally$horizontally$. Atul$Atul$, however, wants to finish up the presentation party soon, hence asks for your help so that he can wrap up things faster.  

-----Input:-----
- First line will contain T$T$, number of test cases. Then the test cases follow. 
- Each testcase contains of a single line of input, three integers N$N$, M$M$ and K$K$.  
- N lines follow, where every line contains M numbers$numbers$ denoting the size of the sugar cube

-----Output:-----
For each test case, output in a single line the maximum votes Atul can get. 

-----Constraints-----
- 1≤T≤$1 \leq T \leq $5
- 1≤N,M≤500$1 \leq N,M \leq 500$
- K≤min(N,M)$K \leq min(N,M)$ 
- 1≤numbers≤109$1 \leq numbers \leq 10^9$

-----Sample Input:-----
1
4 4 3 
1 4 5 7 
2 3 8 6
1 4 8 9 
5 1 5 6 

-----Sample Output:-----
22

-----EXPLANATION:-----
If Atul starts counting votes from (1,4), then he can take the 3 consecutive elements vertically downwards and those are 7,6 and 9 which is the maximum sum possible.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
