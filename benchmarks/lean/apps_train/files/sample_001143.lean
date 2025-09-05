Gorodetskiy is a university student. He is really good at math and really likes solving engaging math problems. In the last exam, his professor gave him really hard math problems to solve, but Gorodetskiy could not solve them and failed the exam, so the professor told him: "These problems are a piece of cake, you should know them from school!" Here is one of the problems from the exam - you can decide if it really was an easy problem or not.
You are given a positive integer $M$. Let's call a positive integer $A$ an interesting number if there is at least one integer $B$ ($A \le B$) such that $A \cdot B$ is divisible by $M$ and $\frac{A \cdot B}{M} = A+B$.
Find all interesting numbers. Let's denote the number of such integers by $K$; it is guaranteed that $K \le 3*10^5$.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains a single integer $M$.

-----Output-----
For each test case:
- First, print a line containing a single integer $K$.
- Then, print $K$ lines. For each valid $i$, the $i$-th of these lines should contain a single integer ― the $i$-th interesting number in increasing order.

-----Constraints-----
- $1 \le T \le 10$
- $1 \le M \le 10^{14}$

-----Subtasks-----
Subtask #1 (20 points): $1 \le M \le 100$
Subtask #2 (20 points): $1 \le M \le 10^7$
Subtask #3 (60 points): original constraints

-----Example Input-----
2
3
6

-----Example Output-----
2
4
6
5
7
8
9
10
12

-----Explanation-----
Example case 1: There are two interesting numbers, $4$ and $6$. For $A = 4$, we can choose $B = 12$ and for $A = 6$, we can choose $B = 6$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
