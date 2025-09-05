Denis was very sad after Nastya rejected him. So he decided to walk through the gateways to have some fun. And luck smiled at him! When he entered the first courtyard, he met a strange man who was selling something. 

Denis bought a mysterious item and it was... Random permutation generator! Denis could not believed his luck.

When he arrived home, he began to study how his generator works and learned the algorithm. The process of generating a permutation consists of $n$ steps. At the $i$-th step, a place is chosen for the number $i$ $(1 \leq i \leq n)$. The position for the number $i$ is defined as follows:

  For all $j$ from $1$ to $n$, we calculate $r_j$  — the minimum index such that $j \leq r_j \leq n$, and the position $r_j$ is not yet occupied in the permutation. If there are no such positions, then we assume that the value of $r_j$ is not defined.  For all $t$ from $1$ to $n$, we calculate $count_t$  — the number of positions $1 \leq j \leq n$ such that $r_j$ is defined and $r_j = t$.  Consider the positions that are still not occupied by permutation and among those we consider the positions for which the value in the $count$ array is maximum.  The generator selects one of these positions for the number $i$. The generator can choose any position. 

Let's have a look at the operation of the algorithm in the following example:

 [Image] 

Let $n = 5$ and the algorithm has already arranged the numbers $1, 2, 3$ in the permutation. Consider how the generator will choose a position for the number $4$:

  The values of $r$ will be $r = [3, 3, 3, 4, \times]$, where $\times$ means an indefinite value.  Then the $count$ values will be $count = [0, 0, 3, 1, 0]$.  There are only two unoccupied positions in the permutation: $3$ and $4$. The value in the $count$ array for position $3$ is $3$, for position $4$ it is $1$.  The maximum value is reached only for position $3$, so the algorithm will uniquely select this position for number $4$. 

Satisfied with his purchase, Denis went home. For several days without a break, he generated permutations. He believes that he can come up with random permutations no worse than a generator. After that, he wrote out the first permutation that came to mind $p_1, p_2, \ldots, p_n$ and decided to find out if it could be obtained as a result of the generator.

Unfortunately, this task was too difficult for him, and he asked you for help. It is necessary to define whether the written permutation could be obtained using the described algorithm if the generator always selects the position Denis needs.

-----Input-----

The first line contains a single integer $t$ $(1 \leq t \leq 10^5)$  — the number of test cases. Then the descriptions of the test cases follow.

The first line of the test case contains a single integer $n$ $(1 \leq n \leq 10^5)$  — the size of the permutation.

The second line of the test case contains $n$ different integers $p_1, p_2, \ldots, p_n$ ($1 \leq p_i \leq n$)  — the permutation written by Denis.

It is guaranteed that the sum of $n$ over all test cases doesn't exceed $10^5$.

-----Output-----

Print "Yes" if this permutation could be obtained as a result of the generator. Otherwise, print "No".

All letters can be displayed in any case.

-----Example-----
Input
5
5
2 3 4 5 1
1
1
3
1 3 2
4
4 2 3 1
5
1 5 2 4 3

Output
Yes
Yes
No
Yes
No

-----Note-----

Let's simulate the operation of the generator in the first test.

At the $1$ step, $r = [1, 2, 3, 4, 5], count = [1, 1, 1, 1, 1]$. The maximum value is reached in any free position, so the generator can choose a random position from $1$ to $5$. In our example, it chose $5$.

At the $2$ step, $r = [1, 2, 3, 4, \times], count = [1, 1, 1, 1, 0]$. The maximum value is reached in positions from $1$ to $4$, so the generator can choose a random position among them. In our example, it chose $1$.

At the $3$ step, $r = [2, 2, 3, 4, \times], count = [0, 2, 1, 1, 0]$. The maximum value is $2$ and is reached only at the $2$ position, so the generator will choose this position.

At the $4$ step, $r = [3, 3, 3, 4, \times], count = [0, 0, 3, 1, 0]$. The maximum value is $3$ and is reached only at the $3$ position, so the generator will choose this position.

At the $5$ step, $r = [4, 4, 4, 4, \times], count = [0, 0, 0, 4, 0]$. The maximum value is $4$ and is reached only at the $4$ position, so the generator will choose this position.

In total, we got a permutation of $2, 3, 4, 5, 1$, that is, a generator could generate it.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded