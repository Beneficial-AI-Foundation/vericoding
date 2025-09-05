People in Karunanagar are infected with Coronavirus. To understand the spread of disease and help contain it as early as possible, Chef wants to analyze the situation in the town. Therefore, he does the following:
- Chef represents the population of Karunanagar as a binary string of length $N$ standing in a line numbered from $1$ to $N$ from left to right, where an infected person is represented as $1$ and an uninfected person as $0$.
- Every day, an infected person in this binary string can infect an adjacent (the immediate left and right) uninfected person.
- Therefore, if before Day 1, the population is $00100$, then at the end of Day 1, it becomes $01110$ and at the end of Day 2, it becomes $11111$.
But people of Karunanagar are smart and they know that if they 'socially isolate' themselves as early as possible, they reduce the chances of the virus spreading. Therefore on $i$-th day, person numbered $P_i$ isolates himself from person numbered $P_i - 1$, thus cannot affect each other. This continues in the town for $D$ days.
Given the population binary string before Day 1, Chef wants to calculate the total number of infected people in Karunanagar at the end of the day $D$. Since Chef has gone to wash his hands now, can you help do the calculation for him?

-----Input:-----
- First line will contain $T$, number of testcases. Then the test cases follow. 
- The first line of each test case contains a single integer $N$ denoting the length of the binary string.
- The next line contains a binary string of length $N$ denoting the population before the first day, with $1$ for an infected person and $0$ for uninfected.
- The next line contains a single integer $D$ - the number of days people isolate themselves.
- The next line contains $P$ - a list of $D$ distinct space-separated integers where each $P_{i}$ denotes that at the start of $i^{th}$ day, person $P_{i}$ isolated him/herself from the person numbered $P_i-1$.

-----Output:-----
For each test case, print a single integer denoting the total number of people who are infected after the end of $D^{th}$ day.

-----Constraints-----
- $1 \leq T \leq 200$
- $2 \leq N \leq 10^{4}$
- $1 \leq D < N$
- $2 \leq P_{i} \leq N$ for $1 \le i \le D$

-----Subtasks-----
Subtask #1(30 points): $1 \leq T \leq 100$, $2 \leq N \leq 2000$
Subtask #2(70 points): Original Constraints

-----Sample Input:-----
2
9
000010000
3
2 5 8
5
00001
1
5

-----Sample Output:-----
6
1

-----EXPLANATION:-----
For the purpose of this explanation, a social distance can be denoted with a '$|$'.
For the first testcase:
- 
Before Day $1$, the population is: $0|00010000$
- 
Before Day $2$, the population is: $0|001|11000$
- 
Before Day $3$, the population is: $0|011|111|00$
- 
Therefore, after Day $3$, the population will be: $0|111|111|00$
So, there are $6$ infected persons.
For the second testcase:
Before Day $1$, the population is: $0000|1$
Therefore, there is one infected person.

def solve_virus_spread (N : Nat) (init_pop : String) (D : Nat) (isolations : List Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded