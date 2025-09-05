After six days, professor GukiZ decided to give more candies to his students. Like last time, he has $N$ students, numbered $1$ through $N$. Let's denote the number of candies GukiZ gave to the $i$-th student by $p_i$. As GukiZ has a lot of students, he does not remember all the exact numbers of candies he gave to the students. He only remembers the following properties of the sequence $p$:
- The numbers of candies given to each of the first $K$ students ($p_1, p_2, \dots, p_K$) are known exactly.
- All elements of the sequence $p$ are distinct and positive.
- GukiZ didn't give more than $x$ candies to any student (the maximum value in the sequence $p$ is not greater than $x$).
- For each student $i$, there is at least one other student $j$ such that $|p_i - p_j| \le D$.
- The professor gave out the biggest possible total number of candies, i.e. $S = p_1 + p_2 + p_3 + \ldots + p_N$ is maximum possible.
GukiZ would like to know the total number of candies $S$ he had at the beginning. However, times change and after six days, the professor is really tired, so it is possible that there is no sequence $p$ which satisfies the constraints. Can you help GukiZ find the number of candies he gave out, or tell him that he must have made a mistake?

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains four space-separated integers $N$, $K$, $x$, $D$.
- The second line contains $K$ distinct space-separated integers $p_1, p_2, \dots, p_K$.

-----Output-----
For each test case, print a single line containing one integer — the number of candies GukiZ had, or $-1$ if there is no valid sequence $p$.

-----Constraints-----
- $1 \le T \le 50$
- $3 \le N \le 10^9$
- $1 \le K \le \mathrm{min}(N, 2 \cdot 10^4)$ 
- $1 \le x \le 2 \cdot 10^9$
- $1 \le D \le 10^9$
- $1 \le p_i \le x$ for each valid $i$
- All values $p_i$ from input are distinct

-----Subtasks-----
Subtask #1 (15 points): $1 \leq x, N, D \leq 15$ 
Subtask #2 (35 points): $1 \leq x, N, D \leq 10^5$ 
Subtask #3 (50 points): original constraints

-----Example Input-----
2
4 3 5 3
2 1 5
3 2 8 2
3 8

-----Example Output-----
12
-1

-----Explanation-----
Example case 1: There are four students. We know that the first student got $p_1 = 2$ candies, the second student got $p_2 = 1$ and the third got $p_3 = 5$ candies; we don't know the number of candies given to the last student. The maximum possible amount of candies given to some student is $x=5$. The best possible option is giving $p_4=4$ candies to the last student. Then, the fourth constraint (with $D=3$) is satisfied for all students. Only the pair of students $(2, 3)$ have numbers of candies that differ by more than $3$, but still, for each student, there are at least two other students with close enough numbers of candies.
Example case 2: GukiZ made some mistake in distribution and there is no valid sequence $p$. The answer is $-1$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded