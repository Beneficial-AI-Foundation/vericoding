You are a king and you are at war. If the enemy breaks through your frontline you lose.
Enemy can break the line only if the sum of morale of any $K$ continuous soldiers is strictly less than $M$. So, you being a motivational orator decides to boost their morale by giving a speech. On hearing it morale of a soldier multiplies by $X$ which depends on you and your speech (i.e. $X$ can be any positive value) but atmost only $K$ continuous speakers can hear your speech.
N soldiers are standing on the frontline with $A[i]$ morale. 
Determine the minimum number of speeches you need to give.

-----Input:-----
The first line contains three space seperated integers $N,K,M$.
The next line contains $N$ space integers, ith of which denotes the morale of $ith$ soldier.

-----Output:-----
Output the minimum number of speeches required. In case if it is impossible to achieve, print $-1$.

-----Constraints:-----
$1 \leq N,M \leq 10^5$
$1 \leq k \leq N$
$0 \leq Ai \leq 10^5$ 

-----Sample Input:-----
6 2 5
1 1 1 1 1 1

-----Sample Output:-----
2

-----Explanation:-----
We multiply 2nd ,3rd  and 5th,6th by 5. Resulting array will be 1 5 5 1 5 5.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
