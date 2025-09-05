Recently in JEC ants have become huge, the Principal is on a journey to snipe them !!
Principal has limited $N$ practice Bullets to practice so that he can be sure to kill ants.
- The Practice ground has max length $L$.
- There is a Limit X such that if the bullet is fired beyond this, it will destroy and it wont be of any further use.
- Bullet can be reused if fired in a range strictly less than X.
He wants to find minimum number of shots taken to find  the distance X by using $N$ bullets.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single line of input, two integers $N, L$. 

-----Output:-----
For each testcase, output in a single line answer the minimum number of shots to find the distance X.

-----Constraints-----
- $1 \leq T \leq 10$
- $2 \leq N,L \leq 100$
*N is always less than  equal to square root of L

-----Subtasks-----
- 10 points : $ N = 1$
- 40 points : $ N = 2$
- 50 points : Original Constraints.

-----Sample Input:-----
2
1 10
2 10

-----Sample Output:-----
10
4

-----EXPLANATION:-----
- 
There is only single bullet which is to be fired from distance 1 to 10 to get the distance X so in the worst case it can take up to 10 shots to find the distance X.
- 
there are 2 bullets and distance 10 meters suppose if distance X is 10 we can get to that by firing first bullet at 4 then 7 then 9 then  at 10 it will break  it took only 4 turns, and if the distance X was 3, we can get that by firing first bullet at 4 it will get destroyed than we use 2nd bullet at 1 , 2, 3  and 2nd bullet will also break it also took 4 turns. You can check for any position minimum number of turns will be at most 4.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
