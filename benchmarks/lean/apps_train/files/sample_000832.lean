A beautiful sequence is defined as a sequence that do not have any repeating elements in it.
You will be given any random sequence of integers, and you have to tell whether it is a beautiful sequence or not. 

-----Input:-----
- The first line of the input contains a single integer $T$. $T$ denoting the number of test cases. The description of $T$ test cases is as follows.
- The next line of the input contains a single integer $N$. $N$ denotes the total number of elements in the sequence.
- The next line of the input contains $N$ space-separated integers $A1, A2, A3...An$ denoting the sequence.

-----Output:-----
- Print "prekrasnyy"(without quotes) if the given sequence is a beautiful sequence, else print "ne krasivo"(without quotes)
Note: each test case output must be printed on new line

-----Constraints:-----
- $1 \leq T \leq 10^2$
- $1 \leq N \leq 10^3$
- $1 \leq A1, A2, A3...An \leq 10^5$

-----Sample Input:-----
2
4
1 2 3 4
6
1 2 3 5 1 4

-----Sample Output:-----
prekrasnyy
ne krasivo

-----Explanation:-----
- 
As 1st sequence do not have any elements repeating, hence it is a beautiful sequence
- 
As in 2nd sequence the element 1 is repeated twice, hence it is not a beautiful sequence

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded