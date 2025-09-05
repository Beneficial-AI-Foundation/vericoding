The Quark Codejam's number QC(n, m) represents the number of ways to partition a set of n things into m nonempty subsets. For example, there are seven ways to split a four-element set into two parts:

{1, 2, 3} ∪ {4}, {1, 2, 4} ∪ {3}, {1, 3, 4} ∪ {2}, {2, 3, 4} ∪ {1},

{1, 2} ∪ {3, 4}, {1, 3} ∪ {2, 4}, {1, 4} ∪ {2, 3}.

We can compute QC(n, m) using the recurrence,

QC(n, m) = mQC(n − 1, m) + QC(n − 1, m − 1), for integers 1 < m < n.

but your task is a somewhat different: given integers n and m, compute the parity of QC(n, m), i.e. QC(n, m) mod 2.

Example : 

QC(4, 2) mod 2 = 1. 
Write a program that reads two positive integers n and m, computes QC(n, m) mod 2, and writes the

result.

-----Input-----
The input begins with a single positive integer on a line by itself indicating the number of the cases. This line is followed by the input cases.

The input consists two integers n and m separated by a space, with 1 ≤ m ≤ n ≤ 1000000000.

-----Output-----
For each test case, print the output.

The output should be the integer S(n, m) mod 2.
Sample Input
1

4 2
Sample Output
1

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
