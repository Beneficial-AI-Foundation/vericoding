The Fibonacci sequence is defined as F(n) = F(n-1) + F(n-2). You have developed two sequences of numbers. The first sequence that uses the bitwise XOR operation instead of the addition method is called the Xoronacci number. It is described as follows:
X(n) = X(n-1) XOR X(n-2)
The second sequence that uses the bitwise XNOR operation instead of the addition method is called the XNoronacci number. It is described as follows:
E(n) = E(n-1) XNOR E(n-2)
The first and second numbers of the sequence are as follows:
X(1) = E(1) = a
X(2) = E(2) = b
Your task is to determine the value of max(X(n),E(n)), where n is the n th term of the Xoronacci and XNoronacci sequence.

-----Input:-----
The first line consists of a single integer T denoting the number of test cases.
The first and the only line of each test case consists of three space separated integers a, b and n.

-----Output:-----
For each test case print a single integer max(X(n),E(n)).

-----Constraints-----
- $1 \leq T \leq 1000$
- $2 \leq a,b,n \leq 1000000000000$

-----Sample Input:-----
1
3 4 2 

-----Sample Output:-----
4

-----EXPLANATION:-----
Xoronacci Sequence : 3 4 7 …….
XNoronacci Sequence : 3 4 0 …….
Here n = 2. Hence max(X(2),E(2)) = 4

def solve_sequence (a b n : Nat) : Nat := sorry

def bitXor (a b : Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
