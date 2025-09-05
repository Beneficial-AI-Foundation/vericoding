Coach Khaled is a swag teacher in HIT (Hag Institute of Technology). However, he has some obsession problems.
Recently, coach Khaled was teaching a course in building 8G networks using TV antennas and programming them with assembly. There are $N$ students (numbered $1$ through $N$) in his class; for some reason, this number is always a multiple of $4$. The final exam has finished and Khaled has all the scores of his $N$ students. For each valid $i$, the score of the $i$-th student is $A_i$; each score is an integer between $0$ and $100$. Currently, the score-grade distribution is as follows:
- grade D for score smaller than $60$
- grade C for score greater or equal to $60$, but smaller than $75$
- grade B for score greater or equal to $75$, but smaller than $90$
- grade A for score greater or equal to $90$
However, coach Khaled is not satisfied with this. He wants exactly $N/4$ students to receive each grade (A, B, C and D), so that the grades are perfectly balanced. The scores cannot be changed, but the boundaries between grades can. Therefore, he wants to choose three integers $x$, $y$ and $z$ and change the grade distribution to the following (note that initially, $x = 60$, $y = 75$ and $z = 90$):
- grade D for score smaller than $x$
- grade C for score greater or equal to $x$, but smaller than $y$
- grade B for score greater or equal to $y$, but smaller than $z$
- grade A for score greater or equal to $z$
Your task is to find thresholds $x$, $y$ and $z$ that result in a perfect balance of grades. If there are multiple solutions, choose the one with the maximum value of $x+y+z$ (because coach Khaled wants seem smarter than his students); it can be proved that there is at most one such solution. Sometimes, there is no way to choose the thresholds and coach Khaled would resign because his exam questions were low-quality.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output-----
For each test case, if there is no solution, print a single line containing the integer $-1$; otherwise, print a single line containing three space-separated integers $x$, $y$ and $z$.

-----Constraints-----
- $1 \le T \le 1,000$
- $4 \le N \le 100$
- $N$ is divisible by $4$
- $0 \le A_i \le 100$ for each valid $i$
- the sum of $N$ over all test cases does not exceed $5,000$

-----Subtasks-----
Subtask #1 (100 points): original constraints

-----Example Input-----
6
4
90 25 60 75
8
27 29 92 92 67 67 85 92
4
0 1 2 3
4
100 100 100 100
4
30 30 40 50
4
30 40 40 50

-----Example Output-----
60 75 90
-1
1 2 3
-1
-1
-1

-----Explanation-----
Example case 1: The default distribution is the correct one.
Example case 4: All students have the same score and grade, so there is no way to choose the thresholds and coach Khaled must resign.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded