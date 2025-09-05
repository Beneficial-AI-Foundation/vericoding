Taxis of Kharagpur are famous for making sharp turns. You are given the coordinates where a particular taxi was on a 2-D planes at N different moments: (x1, y1), (x2, y2), ..., (xN, yN). In between these coordinates, the taxi moves on a straight line. A turn at the i-th (2 ≤ i ≤ N-1) coordinate is said to be a sharp turn if the angle by which it turns at Point B = (xi, yi) when going from coordinates A = (xi-1, yi-1) to C = (xi+1, yi+1) via (xi, yi) is greater than 45 degrees. ie. suppose you extend the line segment AB further till a point D, then the angle DBC would be greater than 45 degrees.
You have to identify whether the taxi made a sharp turn somewhere or not (Please look at Output section for details). If it made a sharp turn, also identify whether it is possible to change the coordinates at one of the N moments to make sure that the taxi doesn't make any sharp turn. Note that all the N pairs of coordinates (including the new coordinates) should be integers and distinct and should have their x and y coordinates at least 0 and at most 50.

-----Input-----
- The first line of the input contains a single integer T denoting the number of test cases. The description of T test cases follows.
- The first line of each test case contains a single integer N denoting the number of moments at which you are given the information of the taxi's coordinates.
- Each of the next N lines contains two space-separated integers xi and yi denoting the x and y coordinates of the taxi at i-th moment.

-----Output-----
- For each test case, print a single line containing two space-separated strings, either of which can be a "yes" or "no" (without quotes). If there was no sharp turn, the first string should be "yes", and if there was a sharp turn, the first string should be "no". For the second string, you should tell whether it is possible to modify at most one coordinate in such a way that taxi doesn't make a sharp turn. Note that if the first string is "yes", then the second string would always be "yes".

-----Constraints-----
- 1 ≤ T ≤ 50
- 3 ≤ N ≤ 50
- 0 ≤ xi, yi ≤ 50
- It's guaranteed that all (xi, yi) pairs are distinct.

-----Example-----
Input
5
3
0 0
1 1
2 1
3
0 0
1 0
6 1
3
0 0
1 0
1 1
4
0 0
1 0
1 1
6 1
6
0 0
1 0
1 1
2 1
2 2
3 2

Output
yes yes
yes yes
no yes
no yes
no no

-----Explanation-----
Example 1. 

You can see that taxi is never making a sharp turn.

Example 3

You can see that taxi is making a sharp turn of 90 degrees, an angle greater than 45'. However, you can change the coordinates of the third points to (2, 1) to ensure that the angle remains <= 45'.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
