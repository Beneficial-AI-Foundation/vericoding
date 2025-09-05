Let's define the niceness of a sequence of positive integers X1,X2,…,XN$X_1, X_2, \dots, X_N$ as the sum of greatest common divisors of all pairs of its elements, i.e.
N∑i=1N∑j=i+1gcd(Xi,Xj).∑i=1N∑j=i+1Ngcd(Xi,Xj).\sum_{i=1}^N \sum_{j=i+1}^N \mathrm{gcd}(X_i, X_j)\;.
For example, the niceness of the sequence [1,2,2]$[1, 2, 2]$ is gcd(1,2)+gcd(1,2)+gcd(2,2)=4$gcd(1, 2) + gcd(1, 2) + gcd(2, 2) = 4$.
You are given a sequence A1,A2,…,AN$A_1, A_2, \dots, A_N$; each of its elements is either a positive integer or missing.
Consider all possible ways to replace each missing element of A$A$ by a positive integer (not necessarily the same for each element) such that the sum of all elements is equal to S$S$. Your task is to find the total niceness of all resulting sequences, i.e. compute the niceness of each possible resulting sequence and sum up all these values. Since the answer may be very large, compute it modulo 109+7$10^9 + 7$.

-----Input-----
- The first line of the input contains a single integer T$T$ denoting the number of test cases. The description of T$T$ test cases follows.
- The first line of each test case contains two space-separated integers N$N$ and S$S$. 
- The second line contains N$N$ space-separated integers A1,A2,…,AN$A_1, A_2, \dots, A_N$. Missing elements in this sequence are denoted by −1$-1$.

-----Output-----
For each test case, print a single line containing one integer — the total niceness modulo 109+7$10^9 + 7$.

-----Constraints-----
- 1≤T≤20$1 \le T \le 20$
- 1≤N,S≤50$1 \le N, S \le 50$
- 1≤Ai≤50$1 \le A_i \le 50$ or Ai=−1$A_i = -1$ for each valid i$i$

-----Subtasks-----
Subtask #1 (30 points):
- 1≤N,S≤18$1 \le N, S \le 18$
- 1≤Ai≤18$1 \le A_i \le 18$ or Ai=−1$A_i = -1$ for each valid i$i$
Subtask #2 (70 points): original constraints

-----Example Input-----
3
3 3
1 1 -1
4 8
1 -1 -1 3
3 10
-1 -1 -1

-----Example Output-----
3
23
150

-----Explanation-----
Example case 1: There is only one possible way to fill in the missing element; the resulting sequence is [1,1,1]$[1, 1, 1]$. Its niceness is 3$3$.
Example case 2: There is only three possible ways to fill in the missing elements; the resulting sequences are [1,1,3,3]$[1, 1, 3, 3]$, [1,3,1,3]$[1, 3, 1, 3]$, and [1,2,2,3]$[1, 2, 2, 3]$. The sum of their niceness is 8+8+7=23$8 + 8 + 7 = 23$.

def calc_total_niceness (n : Nat) (target_sum : Nat) (nums : List Int) : Nat :=
sorry

def gcd (a b : Nat) : Nat :=
sorry

def list_sum (xs : List Int) : Int :=
sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
