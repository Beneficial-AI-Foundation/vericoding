Being a crewmate in the Among Us game, you will have to solve a task to win against the imposter. 
The task : You are given a certain number of bulbs(Say n) which are initially in OFF position. 
The bulbs are numbered from 1 to n. There will be n current fluctuations in such a way that in the 1st fluctuation all bulbs are toggled, in the 2nd fluctuation every 2nd bulb is toggled, in the 3rd fluctuation every 3rd bulb is toggled and so on.
Your job as a crewmate is to find the number of bulbs which are ON at the end of n fluctuations. But, the imposter has a special power which alerts it when a bulb with a number divisible by 3 is kept ON at the end of n fluctuations. 
So, you will have to switch off the bulbs with numbers divisible by 3 and give the final result to complete the task and win the game.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single line of input, an integer $n$. 

-----Output:-----
- For each testcase, output a single integer - the number of bulbs that will remain ON after $n$ fluctuations.

-----Constraints :-----
- $1 \leq T \leq 1000$
- $2 \leq n \leq 10^9$

-----Sample Input:-----
2
2
20

-----Sample Output:-----
1

3

def solve_bulb_fluctuations (n: Nat) : Nat :=
  sorry

def sqrt (n: Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
