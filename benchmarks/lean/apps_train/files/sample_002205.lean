There are N towns on a line running east-west.
The towns are numbered 1 through N, in order from west to east.
Each point on the line has a one-dimensional coordinate, and a point that is farther east has a greater coordinate value.
The coordinate of town i is X_i.
You are now at town 1, and you want to visit all the other towns.
You have two ways to travel:
 - Walk on the line.
Your fatigue level increases by A each time you travel a distance of 1, regardless of direction.
 - Teleport to any location of your choice.
Your fatigue level increases by B, regardless of the distance covered.
Find the minimum possible total increase of your fatigue level when you visit all the towns in these two ways.

-----Constraints-----
 - All input values are integers.
 - 2≤N≤10^5
 - 1≤X_i≤10^9
 - For all i(1≤i≤N-1), X_i<X_{i+1}.
 - 1≤A≤10^9
 - 1≤B≤10^9

-----Input-----
The input is given from Standard Input in the following format:
N A B
X_1 X_2 ... X_N

-----Output-----
Print the minimum possible total increase of your fatigue level when you visit all the towns.

-----Sample Input-----
4 2 5
1 2 5 7

-----Sample Output-----
11

From town 1, walk a distance of 1 to town 2, then teleport to town 3, then walk a distance of 2 to town 4.
The total increase of your fatigue level in this case is 2×1+5+2×2=11, which is the minimum possible value.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded
