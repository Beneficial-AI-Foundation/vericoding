Rohit has n empty boxes lying on the ground in a line. The size of the boxes is given in the form of an array $a$. The size of the ith box is denoted by $a[i]$. Since Rohit has a tiny room, there is a shortage of space. Therefore, he has to reduce the number of boxes on the ground by putting a box into another box that is at least twice the size of the current box i.e if we have to put the ith box into the jth box then $( 2*a[i] ) <= a[j]$.
Each box can contain a maximum of one box and the box which is kept in another box cannot
hold any box itself.
Find the minimum number of boxes that will remain on the ground after putting boxes into each other.

-----Input:-----
- The first line contains a single integer n.
- The next n lines contain the integer a[i] - the size of the i-th box.

-----Output:-----
Output a single integer denoting the minimum number of boxes remaining on the ground.

-----Constraints-----
- $1 \leq n \leq 5*10^5$
- $1 \leq a[i] \leq 10^5$

-----Subtasks-----
- 30 points : $1 \leq n \leq 10^2$
- 70 points : $1 \leq n \leq 5*10^5$

-----Sample Input:-----
5
16
1
4
8
2

-----Sample Output:-----
3

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
