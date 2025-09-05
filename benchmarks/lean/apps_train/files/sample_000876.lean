Sereja have array A' that contain N integers. Now Sereja want to permute elements of the array, he want to use some permutation p, such that A[i] = A'[p[i]], where A - new array. 

Lets function f(A,i) = S - A[i] - A[i +1] - ... - A[j], where j is the maximum possible index, such that A[i] + A[i + 1] + ... + A[j] <= S, if A[i] > S, f(A, i) = S.

Help Sereja to find such permutation p, such that (f(A, 1) + f(A, 2) + ... f(A, k))/k will be as low as possible. 

-----Input-----

First line of input contain integer T - number of testcases. Next lines contain T testcases. First line of each testcase contain three integers N, k, S. Next line contain N integers - array A'.

-----Output-----

For each testcase output N numbers in one line - permutation p. 

-----Constraints-----
- 1 ≤ T ≤ 10
- 1 ≤ N ≤ 2000
- 1 ≤ k ≤ N
- 1 ≤ A'[i] ≤ 10^4
- 1 ≤ S ≤ 10^9

-----Example-----
Input:
2
3 2 4
3 4 1
4 4 1
1 1 1 1

Output:
2 1 3
4 3 2 1

-----Scoring-----

Suppose Sum will be sum of yours (f(A, 1) + f(A, 2) + ... f(A, k))/k per each testcase.  
Lets B will be the smallest such sum. Your score will be equal to B/Sum. Lower scores will earn more points.

We have 20 official test files. You must correctly solve all test files to receive OK. During the contest, your overall score is the sum of the scores on the first 4 test files. After the contest, all solutions will be rescored by the sum of the scores on the rest 16 test files. Note, that public part of the tests may not contain some border cases.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
