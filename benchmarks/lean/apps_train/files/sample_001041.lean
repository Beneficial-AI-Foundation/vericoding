Chef is making Window frames for his new office, for this he has  n wooden Logs whose lengths are l1, l2, … ln respectively. Chef Doesn’t want to break any logs or Stick 2 or more logs together.
To make a  h × w Window Frame, he needs two Logs with lengths equal h and two with length . 
The Chef wants as much sunlight in as possible and for it he has decided to make from the available logs as many frames as possible. Help him in finding the number of window Frames that he can make. 
Note : Chef do not need to use all the logs
Input:
The first line of the input contains a single integer T denoting the number of test cases. The description of each test case follows :.
The first line of each test case contains a single integer n the number of wooden logs. 
The second line contains  n space-separated integers l1,l2,l3….ln The length of each wooden log
Output: 
The only line in Output Contains single Integer denoting the maximum possible number of Wooden Frames.
Constraints:
1 ≤ T ≤ 10
1 ≤ n ≤ 100
1 ≤ li ≤ 10000
Example Input:
2
4
1 2 1 2
8
1 2 1 3 4 1 5 6
Example Output:
1
0
Explanation :
First Case :  We can build a frame of dimension 1x2 as two logs of each dimension are available.
Second Case :  We can’t build any Frame as no logs of length except 1 have more than one piece.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded