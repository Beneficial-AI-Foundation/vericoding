Chef has an array A = (A1, A2, ..., AN), which has N integers in it initially. Chef found that for i ≥ 1, if Ai > 0, Ai+1 > 0, and Ai+2 exists, then he can decrease both Ai, and Ai+1 by one and increase Ai+2 by one. If Ai+2 doesn't exist, but Ai > 0, and Ai+1 > 0, then he can decrease both Ai, and Ai+1 (which will be the currently last two elements of the array) by one and add a new element at the end, whose value is 1.
Now Chef wants to know the number of different arrays that he can make from A using this operation as many times as he wishes. Help him find this, and because the answer could be very large, he is fine with you reporting the answer modulo 109+7.
Two arrays are same if they have the same number of elements and if each corresponding element is the same. For example arrays (2,1,1) and (1,1,2) are different. 

-----Input-----
- The first line of the input contains a single integer T denoting the number of test cases.
- The first line contains a single integer N denoting the initial number of elements in A.
- The second line contains N space-separated integers: A1, A2, ... , AN. 

-----Output-----
For each test case, output answer modulo 109+7 in a single line. 

-----Constraints-----
- 1 ≤ T ≤ 5
- 1 ≤ N ≤ 50
- 0 ≤ Ai ≤ 50

-----Subtasks-----
- Subtask 1 (20 points) : 1 ≤ N ≤ 8, 0 ≤ Ai ≤ 4
- Subtask 2 (80 points) : Original constraints

-----Example-----
Input:
3
3
2 3 1
2
2 2
3
1 2 3

Output:
9
4
9

-----Explanation-----
Example case 1.
We'll list the various single steps that you can take (ie. in one single usage of the operation):
- (2, 3, 1) → (2, 2, 0, 1)
- (2, 2, 0, 1) → (1, 1, 1, 1)
- (1, 1, 1, 1) → (1, 1, 0, 0, 1)
- (1, 1, 0, 0, 1) → (0, 0, 1, 0, 1)
- (1, 1, 1, 1) → (1, 0, 0, 2)
- (1, 1, 1, 1) → (0, 0, 2, 1)
- (2, 3, 1) → (1, 2, 2)
- (1, 2, 2) → (0, 1, 3)

So all the arrays you can possibly get are: 
(2, 3, 1), (2, 2, 0, 1), (1, 1, 1, 1), (1, 1, 0, 0, 1), (0, 0, 1, 0, 1), (1, 0, 0, 2), (0, 0, 2, 1), (1, 2, 2), and (0, 1, 3)
Since there are 9 different arrays that you can reach, the answer is 9.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
