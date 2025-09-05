You are given an array $a$ of length $n$. A subsequence of this array is valid, if it satisfies these two conditions:
- There shouldn't be any two even numbers within a distance of $K$, both which have been chosen in the subsequence. i.e. there shouldn't be two indices $i, j$ such that $a_i$ and $a_j$ are even, $|i - j| \leq K$ and $a_i$ and $a_j$ are in the subsequence. 
- Similarly, there shouldn't be any two odd numbers within a distance of $K$, both which have been chosen in the subsequence
The sum of a subsequence is the sum of all the numbers in it. Your task is find the maximum sum possible in a valid subsequence of the given array. Print this maximum sum.

-----Input-----
- The first line of the input contains an integer $T$ denoting the number of test cases. The description of the test cases follows.
- The first line of each test case contains two space-separated integers $n, k$.
- The second line of each test case contains $n$ space-separated integers denoting the array $a$.

-----Output-----
For each test case, output an integer corresponding to the answer of the problem.

-----Constraints-----
- $1 \le T \le 10^5$
- $1 \le n \leq 10^5$
- $1 \le k \leq  n$
- $1 \le a_i \leq 10^9$
- Sum of $n$ over all the test cases doesn't exceed $10^6$

-----Example Input-----
3
1 1
3
2 1
2 2
5 2
1 2 3 4 6

-----Example Output-----
3
2
11

-----Explanation:-----
Testcase 2: Only one of the two 2s can be chosen. Hence the answer is 2.
Testcase 3: The subsequence containing the second, third and fifth numbers is a valid subsequence, and its sum is 2+3+6 = 11. You can check that this is the maximum possible, and hence is the answer.

def List.sum (xs : List Nat) : Nat :=
match xs with
| [] => 0
| x :: xs => x + List.sum xs

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded