You are given a string $S$ and an integer $L$. A operation is described as :- "You are allowed to pick any substring from first $L$ charcaters of $S$, and place it at the end of the string $S$. 
A string $A$ is a substring of an string $B$ if $A$ can be obtained from $B$ by deletion of several (possibly, zero or all) characters from the beginning and several (possibly, zero or all) elements from the end.
Find the lexographically smallest string after performing this opertaion any number of times (possibly zero).
For example $S$ = "codechef" and $L=4$. Then, we can take substring "ode" from S[0-3] and place it at end of the string $S$ = "cchefode".

-----Input:-----
- First line will contain $T$, number of testcases. 
- Then each of the N lines contain an integer $L$ and a string $S$. 

-----Output:-----
For each testcase, output in a single line answer lexographically smallest string.

-----Constraints-----
- $1 \leq T \leq 10^4$
- $2 \leq |S| \leq 10^3$
- $1 \leq L \leq N $

-----Sample Input:-----
2
1 rga
2 cab

-----Sample Output:-----
arg
abc

-----EXPLANATION:-----
In the first testcase:
substring 'r' is picked and placed at the end of the string. rga -> gar
Then performing same operation gives :- gar -> arg

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded