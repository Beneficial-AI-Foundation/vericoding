Chefu is Chef's little brother, he is 12 years old and he is new to competitive programming.
Chefu is practicing very hard to become a very skilled competitive programmer and win gold medal in IOI.
Now Chefu is participating in a contest and the problem that he is trying to solve states:
Given an array A of N integers, find any i, j such that i <  j 
and Ai + Aj is maximum possible 
unfortunately, there's no much time left before the end of the contest, so Chefu doesn't have time to think of correct solution, so instead, he wrote a solution that selects a random pair (i,  j) (i <  j) and output Ai + Aj. each pair is equiprobable to be selected.
Now Chefu wants your help to calculate the probability that his solution will pass a particular input.

-----Input-----
First line contains an integer T denoting the number of test-cases.
First line of each test-case contains a single integer N
Second line of each test-case contains N space-separated integers A1 A2 ... AN

-----Output-----
For each test-case output a single line containing a single number denoting the probability that Chefu's solution to output a correct answer. your answer will be accepted if the absolute difference between it and correct answer is less than 1e-6

-----Constraints-----
- 1 ≤ T ≤ 100
- 2 ≤ N ≤ 100
- 1 ≤ Ai ≤ 1,000

-----Example-----
Input:
3
4
3 3 3 3
6
1 1 1 2 2 2
4
1 2 2 3

Output:
1.00000000
0.20000000
0.33333333

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible