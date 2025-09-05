Give me Biscuit

Sunny wants to make slices of biscuit of size c * d into identical pieces.

but each piece is a square having maximum possible side length with no left over piece of biscuit.

Input Format

The first line contains an integer N.

N lines follow. Each line contains two space separated integers c and d.

which denote length and breadth of the biscuit.

Constraints

1 <= N <= 1000

1 <= c,d <= 1000
Output Format

N lines, each containing an integer that denotes the number of squares of maximum size, when the biscuit is cut as per the given condition.

Sample Input 

2

2 2

6 9

Sample Output 

1

6

Explanation 

The 1st testcase has a biscuit whose original dimensions are 2 X 2, the biscuit is uncut and is a square.

Hence the answer is 1.

The 2nd testcase has a biscuit of size 6 X 9 . We can cut it into 54 squares of size 1 X 1 , 6 of size 3 X 3 . For other sizes we will have leftovers.

Hence, the number of squares of maximum size that can be cut is 6.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible