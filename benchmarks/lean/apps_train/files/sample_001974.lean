There are N people, conveniently numbered 1 through N.
We want to divide them into some number of groups, under the following two conditions:
 - Every group contains between A and B people, inclusive.
 - Let F_i be the number of the groups containing exactly i people. Then, for all i, either F_i=0 or C≤F_i≤D holds.
Find the number of these ways to divide the people into groups.
Here, two ways to divide them into groups is considered different if and only if there exists two people such that they belong to the same group in exactly one of the two ways.
Since the number of these ways can be extremely large, print the count modulo 10^9+7.

-----Constraints-----
 - 1≤N≤10^3
 - 1≤A≤B≤N
 - 1≤C≤D≤N

-----Input-----
The input is given from Standard Input in the following format:
N A B C D

-----Output-----
Print the number of ways to divide the people into groups under the conditions, modulo 10^9+7.

-----Sample Input-----
3 1 3 1 2

-----Sample Output-----
4

There are four ways to divide the people:
 - (1,2),(3)
 - (1,3),(2)
 - (2,3),(1)
 - (1,2,3)
The following way to divide the people does not count: (1),(2),(3). This is because it only satisfies the first condition and not the second.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded
