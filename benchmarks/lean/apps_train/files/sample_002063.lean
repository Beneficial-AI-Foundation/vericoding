One of Timofey's birthday presents is a colourbook in a shape of an infinite plane. On the plane n rectangles with sides parallel to coordinate axes are situated. All sides of the rectangles have odd length. Rectangles cannot intersect, but they can touch each other.

Help Timofey to color his rectangles in 4 different colors in such a way that every two rectangles touching each other by side would have different color, or determine that it is impossible.

Two rectangles intersect if their intersection has positive area. Two rectangles touch by sides if there is a pair of sides such that their intersection has non-zero length [Image] The picture corresponds to the first example 

-----Input-----

The first line contains single integer n (1 ≤ n ≤ 5·10^5) — the number of rectangles.

n lines follow. The i-th of these lines contains four integers x_1, y_1, x_2 and y_2 ( - 10^9 ≤ x_1 < x_2 ≤ 10^9,  - 10^9 ≤ y_1 < y_2 ≤ 10^9), that means that points (x_1, y_1) and (x_2, y_2) are the coordinates of two opposite corners of the i-th rectangle.

It is guaranteed, that all sides of the rectangles have odd lengths and rectangles don't intersect each other.

-----Output-----

Print "NO" in the only line if it is impossible to color the rectangles in 4 different colors in such a way that every two rectangles touching each other by side would have different color.

Otherwise, print "YES" in the first line. Then print n lines, in the i-th of them print single integer c_{i} (1 ≤ c_{i} ≤ 4) — the color of i-th rectangle.

-----Example-----
Input
8
0 0 5 3
2 -1 5 0
-3 -4 2 -1
-1 -1 2 0
-3 0 0 5
5 2 10 3
7 -3 10 2
4 -2 7 -1

Output
YES
1
2
2
3
2
2
4
1

def colorRectangles (rectangles : List (Int × Int × Int × Int)) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded