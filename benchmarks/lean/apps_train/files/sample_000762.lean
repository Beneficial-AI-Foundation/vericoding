Xorgon is an extremely delicious treat formed by the sequence $S$ of binary integers $s_1, s_2,..,s_N$. A really interesting property found in a Xorgon is that the xor of all elements in any contiguous subsequence of length $K$ in $S$ will result in $1$.   
Chef has been asked to prepare a Xorgon. However, he has at his disposal a binary sequence $X$ containing the binary integers $x_1, x_2, ...x_N$. To prepare a Xorgon, the chef may flip the value of as many binary digits in $X$ as required.(i.e. turn a $1$ to a $0$ and $0$ to a $1$). Unfortunately, flipping a digit takes a lot of time and the chef has to serve many orders. Can you help the chef calculate the minimum number of flips required to cook a Xorgon from the given $X$?

-----Input:-----
- The first line will contain two space-separated integers $N, K$.
- Next line contains N space-separated integers $x_1, x_2, ...,x_N$. 

-----Output:-----
Output in a single line minimum number of flips required to turn $X$ into a Xorgon.

-----Constraints-----
- $1 \leq K \leq N \leq 3*10^6$
- $0 \leq x_i \leq 1$

-----Sample Input:-----
7 5
1 0 0 1 1 1 1

-----Sample Output:-----
1

-----EXPLANATION:-----
Flip the last bit from 1 to 0 to obtain a Xorgon.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible