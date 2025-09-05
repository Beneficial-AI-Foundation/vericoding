Shashank is playing a game with his friends.
There are n sticks located in a row at points $a_1,a_2, ...,a_n$. Each stick has a height- $h_i$. A person can chop a stick down, after which it takes over one of the regions [$a_i$ - $h_i$, $a_i$] or [$a_i$, $a_i$ + $h_i$]. The stick that is not chopped remains at the point $a_i$. A person can chop a stick in a particular direction if the region to be taken up by the chopped stick does not overlap with an already existing point. The winner $($s$)$ of the game will be one or more people who can answer the question: What is the maximum number of sticks that can be chopped?
Shashank wants to win the game and hence he needs needs your help in finding out what is the maximum number of sticks that can be chopped down.

-----Input:-----
- The first line of each input contains a single integer n.
- n lines follow. Each of the n lines contain a pair of integers: $a_i,h_i$.

-----Output:-----
Output in a single line answer- the maximum number of sticks that can be chopped down.

-----Constraints-----
- $1 \leq n \leq 10^5$
- $1 \leq a_i,h_i \leq 10^9$
- The pairs are given in the order of ascending $a_i$. No two sticks are located at the same point.

-----Sample Input 1:-----
5
1 2
2 1
5 10
10 9
19 1

-----Sample Input 2:-----
5
1 2
2 1
5 10
10 9
20 1

-----Sample Output 1:-----
3

-----Sample Output 2:-----
4

-----EXPLANATION:-----
In the first example you can fell the sticks as follows:
- chop the stick 1 to the left — now it will take over the region $[ - 1;1]$
- chop the stick 2 to the right — now it will take over the region $[2;3]$
- spare the stick 3— it will take over the point $5$
- spare the stick 4— it will take over the point $10$
- chop the stick 5 to the right — now it will take over the region $[19;20]$

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
