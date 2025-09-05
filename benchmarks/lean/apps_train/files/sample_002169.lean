In the State of Takahashi in AtCoderian Federation, there are N cities, numbered 1, 2, ..., N.
M bidirectional roads connect these cities.
The i-th road connects City A_i and City B_i.
Every road connects two distinct cities.
Also, for any two cities, there is at most one road that directly connects them.
One day, it was decided that the State of Takahashi would be divided into two states, Taka and Hashi.
After the division, each city in Takahashi would belong to either Taka or Hashi.
It is acceptable for all the cities to belong Taka, or for all the cities to belong Hashi.
Here, the following condition should be satisfied:
 - Any two cities in the same state, Taka or Hashi, are directly connected by a road.
Find the minimum possible number of roads whose endpoint cities belong to the same state.
If it is impossible to divide the cities into Taka and Hashi so that the condition is satisfied, print -1.

-----Constraints-----
 - 2 \leq N \leq 700
 - 0 \leq M \leq N(N-1)/2
 - 1 \leq A_i \leq N
 - 1 \leq B_i \leq N
 - A_i \neq B_i
 - If i \neq j, at least one of the following holds: A_i \neq A_j and B_i \neq B_j.
 - If i \neq j, at least one of the following holds: A_i \neq B_j and B_i \neq A_j.

-----Input-----
Input is given from Standard Input in the following format:
N M
A_1 B_1
A_2 B_2
:
A_M B_M

-----Output-----
Print the answer.

-----Sample Input-----
5 5
1 2
1 3
3 4
3 5
4 5

-----Sample Output-----
4

For example, if the cities 1, 2 belong to Taka and the cities 3, 4, 5 belong to Hashi, the condition is satisfied.
Here, the number of roads whose endpoint cities belong to the same state, is 4.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible