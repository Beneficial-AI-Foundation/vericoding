Chef had an array A with length N, but some of its elements got lost. Now, each element of this array is either unknown (denoted by -1) or a positive integer not exceeding K.
Chef decided to restore the array A by replacing each unknown element by a positive integer not exceeding K.
However, Chef has M restrictions that must hold for the restored array. There are two types of restrictions:

- I L R, meaning that for each i such that L < i ≤ R, the condition Ai - Ai-1 = 1 should be satisfied.
- D L R, meaning that for each i such that L < i  ≤ R, the condition Ai - Ai-1 = -1 should be satisfied.

Chef would like to know the number of ways to restore the array while satisfying all restrictions, modulo 109+7.

-----Input-----
- The first line of the input contains a single integer T denoting the number of test cases. The description of T test cases follows.
- The first line of each test case contains three space-separated integers N, M and K.
- The second line contains N integers A1, A2, ..., AN.
- Each of the following M lines contains one restriction in the form I L R or D L R.

-----Output-----
For each test case, print a single line containing one integer - the number of ways to restore the array modulo 109+7.

-----Constraints-----
- 1 ≤ T ≤ 10
- 1 ≤ N, M ≤ 100,000
- 1 ≤ K ≤ 1,000,000,000
- 1 ≤ L < R ≤ N
- 1 ≤ Ai ≤ K or Ai = -1 for each valid i
- 1 ≤ sum of N over all test cases ≤ 500,000
- 1 ≤ sum of M over all test cases ≤ 500,000

-----Example-----
Input:

3
4 2 10
2 3 5 4
I 1 2 
D 3 4
5 2 10
-1 -1 -1 -1 -1
I 1 3
D 3 5
6 2 2
-1 -1 -1 -1 -1 -1
I 1 4
D 4 6

Output:

1
8
0

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded