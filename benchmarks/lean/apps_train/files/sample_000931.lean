You are given an array with $N$ integers: $A[1], A[2], \ldots, A[N]$ (where $N$ is even). You are allowed to permute the elements however you want. Say, after permuting the elements, you end up with the array $A'[1], A'[2], \ldots, A'[N]$. Your goal is to maximize the following sum:
|A′[1]−A′[2]| + |A′[3]−A′[4]| + ... + |A′[N−1]−A′[N]||A′[1]−A′[2]| + |A′[3]−A′[4]| + ... + |A′[N−1]−A′[N]|
|A'[1] - A'[2]| \ + \ |A'[3] - A'[4]| \ + \ ... \ + \ |A'[N - 1] - A'[N]|

Here, $|x|$ denotes the absolute value of $x$.
You have to print the maximum sum achievable.

-----Input-----
- The first line contains $T$, the number of test cases.
- Each test case starts with an integer $N$ in the first line.
- The second line of each test case contains $N$ space separated integers, denoting the values of array $A$.

-----Output-----
For each test case, output the maximum sum achievable in a new line.

-----Constraints-----
- $1 \le T \le 10^5$
- $1 \le N \le 10^5$
- $N$ is even
- $|A[i]| \le 10^9$
- Sum of $N$ over all test cases $\le 2 * 10^5$

-----Example Input 1-----
1
4
1 -3 2 -3

-----Example Output 1-----
9

-----Explanation 1-----
The original array is {$1, -3, 2, -3$}. Suppose you permute it and get the array {$2, 1, -3, -3$}. Then the corresponding sum would be $|2 - 1| \ + \ |-3 - (-3)| = 1 + 0 = 1$.
But suppose you permute it differently and get the array {$-3, 2, 1, -3$}. Then the corresponding sum would be $|-3 - 2| \ + \ |1 - (-3)| = 5 + 4 = 9$. You can check that you cannot do any better, and hence the answer is 9.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
