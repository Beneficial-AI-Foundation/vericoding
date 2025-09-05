Raju has created a program to find the square root of a number. But his program can store only integers. Being a newbie, he didn't know about rounding the numbers. Hence his program returns the absolute value of the result if possible. For example, sqrt(3) = 1.73205080757……. His program will return 1
Given a number $N$, and it's integral square root $S$, His instructor will consider the answer correct if Difference between $N$ and the square of $S$ is within less than or equal to $X$% of $N$.

-----Input:-----
- First line contains $T$ no. of test cases and $X$ separated by space
- For every test case, a line contains an integer $N$

-----Output:-----
For every test case, print yes  if his programs return square root and (N-(S^2)) <= 0.01XN . For everything else, print no on a new line

-----Constraints-----
10 points:
- $1 \leq T \leq 10$
- $0\leq N \leq 10$
20 points:
- $1 \leq T \leq 30000$
- $-10^9 \leq N \leq 10^9$
70 points:
- $1 \leq T \leq 10^6$
- $-10^9 \leq N \leq 10^9$

-----Sample Input:-----
2 20
5
3

-----Sample Output:-----
yes
no

-----EXPLANATION:-----
In #1, sqrt(5) = 2.2360679775. Taking integral value, S = 2.

S2 = 4. Difference=1 which is within 20% of 5
In #1, sqrt(3) = 1.73205080757. Taking integral value, S = 1.

S2 = 1. Difference=2  which is not within 20% of 3

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
