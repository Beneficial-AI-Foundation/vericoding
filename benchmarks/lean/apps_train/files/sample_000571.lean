On a planet called RUIZ LAND, which is ruled by the queen, Erika Ruiz. Each person on that planet has a strength value (strength value >0).
That planet has a special rule made by the queen that a boy and a girl will form a couple if their Hate value is a prime number where $Hate$ is given by the formula:-
Hate = (boy's strength value)  XOR (girl's strength value )
You are given $N$ numbers denoting the strength value of $N$ girls, and each of the $N$ girls has to form a couple with a boy such that sum of $Hate$ value of all the $N$ couples will be minimum.
You need to print the strength value of each boy, Where the boy at index $i$ will form a couple with the girl at index $i$, where $1 \leq i \leq N$.
Assume that you can always find at least one boy having that strength for each girl.

-----Input:-----
- First line will contain $N$, the number of Girls. 
- Next line contains $N$ numbers separated by space denoting strength value for each girl.

-----Output:-----
Print the required $N$ numbers denoting strength of boys.

-----Constraints-----
- $1 \leq N \leq 100000$
- $1 \leq A_i \leq 10^9$ , (where $1 \leq i \leq N$) and $A_i$ denotes strength of i'th girl.

-----Sample Input:-----
2
10 16

-----Sample Output:-----
8 18

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded