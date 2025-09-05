DZY loves planting, and he enjoys solving tree problems.

DZY has a weighted tree (connected undirected graph without cycles) containing n nodes (they are numbered from 1 to n). He defines the function g(x, y) (1 ≤ x, y ≤ n) as the longest edge in the shortest path between nodes x and y. Specially g(z, z) = 0 for every z.

For every integer sequence p_1, p_2, ..., p_{n} (1 ≤ p_{i} ≤ n), DZY defines f(p) as $\operatorname{min}_{i = 1}^{n} g(i, p_{i})$. 

DZY wants to find such a sequence p that f(p) has maximum possible value. But there is one more restriction: the element j can appear in p at most x_{j} times.

Please, find the maximum possible f(p) under the described restrictions.

-----Input-----

The first line contains an integer n (1 ≤ n ≤ 3000).

Each of the next n - 1 lines contains three integers a_{i}, b_{i}, c_{i} (1 ≤ a_{i}, b_{i} ≤ n; 1 ≤ c_{i} ≤ 10000), denoting an edge between a_{i} and b_{i} with length c_{i}. It is guaranteed that these edges form a tree.

Each of the next n lines describes an element of sequence x. The j-th line contains an integer x_{j} (1 ≤ x_{j} ≤ n).

-----Output-----

Print a single integer representing the answer.

-----Examples-----
Input
4
1 2 1
2 3 2
3 4 3
1
1
1
1

Output
2

Input
4
1 2 1
2 3 2
3 4 3
4
4
4
4

Output
3

-----Note-----

In the first sample, one of the optimal p is [4, 3, 2, 1].

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded