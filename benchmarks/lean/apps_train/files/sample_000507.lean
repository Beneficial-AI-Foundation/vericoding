Finally, the pandemic is over in ChefLand, and the chef is visiting the school again. Chef likes to climb the stairs of his school's floor by skipping one step, sometimes chef climbs the stairs one by one. Simply, the chef can take one or 2 steps in one upward movement. There are N stairs between ground and next floor. The chef is on the ground floor and he wants to go to the next floor with Cheffina but, Cheffina asks chef in how many ways, the chef can reach the next floor normally or any combination of skipping one step, where order doesn't matter. 

-----Input:-----
- First-line will contain $T$, the number of test cases. Then the test cases follow. 
- Each test case contains a single line of input, two integers $N$. 

-----Output:-----
For each test case, output in a single line answer as the number of ways.

-----Constraints-----
- $1 \leq T \leq 1000$
- $1 \leq N \leq 10^5$

-----Sample Input:-----
1
3

-----Sample Output:-----
2

-----EXPLANATION:-----
ways: [1,1,1], here chef climb to the next floor, one by one stair.
[1,2], here chef climb to the next floor, one step first and after that 2 stairs at once.
Note, [2,1] consider the same as that of [1,2] hence ignored.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible