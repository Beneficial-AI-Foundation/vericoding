A tennis tournament is about to take place with $N$ players participating in it.
Every player plays with every other player exactly once and there are no ties. That is, every match has a winner and a loser. 
With Naman's birthday approaching, he wants to make sure that each player wins the same number of matches so that nobody gets disheartened.  
Your task is to determine if such a scenario can take place and if yes find one such scenario.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single integer $N$ denoting number of players.

-----Output:-----
- If it's impossible for everyone to win the same number of matches, print "NO" (without quotes).
- Otherwise print "YES" (without quotes) and then print $N$ lines , each line should consist of a string containing only 0s and 1s and should be of size $N$. 
- If the jth character in the ith line is 1 then it means in the match between $i$ and $j$ , $i$ wins. 
- You will get a WA if the output does not correspond to a valid tournament, or if the constraints are not satisfied.
- You will get also WA verdict if any 2 lines have contradicting results or if a player beats himself.

-----Constraints-----
- $1 \leq T \leq 100$
- $2 \leq N \leq 100$

-----Subtasks-----
- 10 points : $2 \leq N \leq 6$
- 90 points :  Original Constraints. 

-----Sample Input:-----
2
3
2

-----Sample Output:-----
YES
010
001
100
NO

-----Explanation:-----
One such scenario for $N$ = $3$ is when player $1$ beats player $2$, player $2$ to beats player $3$ and player $3$ beats player $1$. Here all players win exactly $1$ match.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
