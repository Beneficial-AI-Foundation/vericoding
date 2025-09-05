Its Christmas time and Santa has started his ride to deliver gifts to children waiting for him in a 1-dimentional city. All houses in this city are on a number line numbered as 1, 2, 3… and so on. Santa wants to deliver to houses from n to m, but he found that all the kids living at positions that are divisible by a, a+d, a+2d, a+3d or a+4d are naughty and he does not want to deliver them any gifts. Santa wants to know how many gifts he has to carry before leaving to the city given that there is only one kid in a house. Help him out!
Formally, Given $m, n, a, d \in \mathbb{N}$ where $n < m$, find the number of $x \in \{n, n+1, ..., m-1, m\}$ such that $x$ is not divisible by $a$, $a+d$, $a+2d$, $a+3d$ or $a+4d$

-----Input-----
The first line is the number $t$, corresponding to number of test cases\
This is followed by $t$ lines of the format: $n$ $m$ $a$ $d$

-----Output-----
For each test case, print a single number that is the number of gifts Santa should pack.

-----Constraints-----
- $1 < m, n, a \leq 2^{32}$
- $1 < d \leq 2^{10}$

-----Sample Input:-----
1
2 20 2 1

-----Sample Output:-----
5

-----Explanation:-----
In the range {2, 3, 4, …, 19, 20}, only {7, 11, 13, 17, 19} are not divisible by 2, 3, 4, 5, or 6

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded