Chef has N laddus of K sweetness each. Chef wants to eat all laddus, but Chef is restricted with the given condition that he must not eat two adjacent laddus. Chef starts calculating the maximum sweetness that he will get from the laddus. Find the maximum sweetness that chef gets at the end of all calculations. 

-----Input:-----
- First-line will contain $T$, the number of test cases. Then the test cases follow. 
- Each test case contains a single line of input, two integers $N, K$. 

-----Output:-----
For each test case, output in a single line answer as Maximum sweetness the chef will have.

-----Constraints-----
- $1 \leq T \leq 10^5$
- $1 \leq N \leq 10^5$
- $1 \leq K \leq 10^5$

-----Sample Input:-----
2
1 2
4 3

-----Sample Output:-----
2
6

-----EXPLANATION:-----
For 1) Chef will get only 1 laddu with sweetness 2.
For 2) Chef will have multiple ways as
[1,3], [2,4], [1,4] with sweetness 6
[1],[2],[3],[4] with sweetness 3.
Maximum sweetness will be 6.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible