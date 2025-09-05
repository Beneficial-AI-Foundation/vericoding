Given a set of  N  natural numbers 1,2,3........N and Q query.For each query you have to calculate the total number of subset in which  Ith.
number of set come at Kth postion.Elements of every subset should be in sorted order.
The answer could  be very large so you have to print answer modulo 1e9+7.

-----Input:-----
- The first line of input cotains a single integer T denoting the number of test cases.
- For every test case it contains two number N and Q.
- Next Q line contains two number I and K.

-----Output:-----
For each test case print required answer.

-----Constraints and Subtasks:-----
- 1<=T<=5
- 1<=N, K<=4000
- 1<=Q<=1000000
Subtask 3: 5 points
- 1<=T<=5
- 1<=N, K<=16
- 1<=Q<=1000
Subtask 1: 25 points
- T=1
- 1<=N, K<=4000
- 1<=Q<=100000
Subtask 2: 70 points
- Original Constraints.

-----Example:-----
Input:

1

3 3

1 2

2 1

3 2

Output:

0

2

2

-----Explanation:-----
For N=3

total subsets are:

{1}

{2}

{3}

{1,2}

{1,3}

{2,3}

{1,2,3}

Now we can see that for I=1 and K=2 there is no subset in which 1 come at 2nd position so the answer is Zero for that query.

For 2nd query I=2 and K=1 there are two subset i.e {2,3} and {2} in which 2 come at 1st position.

Same for 3rd querry there is two subset i.e{1,3} and {2,3}.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
