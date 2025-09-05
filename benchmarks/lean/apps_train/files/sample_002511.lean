=====Problem Statement=====
There is a horizontal row of n cubes. The length of each cube is given. You need to create a new vertical pile of cubes. The new pile should follow these directions: if cube_i is on top of cube_j then sideLength_j ≥ sideLength_i.
When stacking the cubes, you can only pick up either the leftmost or the rightmost cube each time. Print "Yes" if it is possible to stack the cubes. Otherwise, print "No". Do not print the quotation marks. 

=====Input Format=====
The first line contains a single integer T, the number of test cases.
For each test case, there are 2 lines.
The first line of each test case contains n, the number of cubes.
The second line contains n space separated integers, denoting the sideLengths of each cube in that order. 

=====Constraints=====
1≤T≤5
1≤n≤10^5
1≤sideLength≤2^31

=====Output Format=====
For each test case, output a single line containing either "Yes" or "No" without the quotes.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
