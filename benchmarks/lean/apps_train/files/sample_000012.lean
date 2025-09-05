Once again, Boris needs the help of Anton in creating a task. This time Anton needs to solve the following problem:

There are two arrays of integers $a$ and $b$ of length $n$. It turned out that array $a$ contains only elements from the set $\{-1, 0, 1\}$.

Anton can perform the following sequence of operations any number of times:  Choose any pair of indexes $(i, j)$ such that $1 \le i < j \le n$. It is possible to choose the same pair $(i, j)$ more than once.   Add $a_i$ to $a_j$. In other words, $j$-th element of the array becomes equal to $a_i + a_j$. 

For example, if you are given array $[1, -1, 0]$, you can transform it only to $[1, -1, -1]$, $[1, 0, 0]$ and $[1, -1, 1]$ by one operation.

Anton wants to predict if it is possible to apply some number (zero or more) of these operations to the array $a$ so that it becomes equal to array $b$. Can you help him?

-----Input-----

Each test contains multiple test cases. 

The first line contains the number of test cases $t$ ($1 \le t \le 10000$). The description of the test cases follows.

The first line of each test case contains a single integer $n$ ($1 \le n \le 10^5$)  — the length of arrays.

The second line of each test case contains $n$ integers $a_1, a_2, \dots, a_n$ ($-1 \le a_i \le 1$)  — elements of array $a$. There can be duplicates among elements.

The third line of each test case contains $n$ integers $b_1, b_2, \dots, b_n$ ($-10^9 \le b_i \le 10^9$)  — elements of array $b$. There can be duplicates among elements.

It is guaranteed that the sum of $n$ over all test cases doesn't exceed $10^5$.

-----Output-----

For each test case, output one line containing "YES" if it's possible to make arrays $a$ and $b$ equal by performing the described operations, or "NO" if it's impossible.

You can print each letter in any case (upper or lower).

-----Example-----
Input
5
3
1 -1 0
1 1 -2
3
0 1 1
0 2 2
2
1 0
1 41
2
-1 0
-1 -41
5
0 1 -1 1 -1
1 1 -1 1 -1

Output
YES
NO
YES
YES
NO

-----Note-----

In the first test-case we can choose $(i, j)=(2, 3)$ twice and after that choose $(i, j)=(1, 2)$ twice too. These operations will transform $[1, -1, 0] \to [1, -1, -2] \to [1, 1, -2]$

In the second test case we can't make equal numbers on the second position.

In the third test case we can choose $(i, j)=(1, 2)$ $41$ times. The same about the fourth test case.

In the last lest case, it is impossible to make array $a$ equal to the array $b$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
