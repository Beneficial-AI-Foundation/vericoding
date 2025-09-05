Mandarin chinese
, Russian and Vietnamese as well.
Chef is organising a contest with $P$ problems (numbered $1$ through $P$). Each problem has $S$ subtasks (numbered $1$ through $S$).
The difficulty of a problem can be calculated as follows:
- Let's denote the score of the $k$-th subtask of this problem by $SC_k$ and the number of contestants who solved it by $NS_k$.
- Consider the subtasks sorted in the order of increasing score.
- Calculate the number $n$ of valid indices $k$ such that $NS_k > NS_{k + 1}$.
- For problem $i$, the difficulty is a pair of integers $(n, i)$.
You should sort the problems in the increasing order of difficulty levels. Since difficulty level is a pair, problem $a$ is more difficult than problem $b$ if the number $n$ is greater for problem $a$ than for problem $b$, or if $a > b$ and $n$ is the same for problems $a$ and $b$.

-----Input-----
- The first line of the input contains two space-separated integers $P$ and $S$ denoting the number of problems and the number of subtasks in each problem.
- $2P$ lines follow. For each valid $i$, the $2i-1$-th of these lines contains $S$ space-separated integers $SC_1, SC_2, \dots, SC_S$ denoting the scores of the $i$-th problem's subtasks, and the $2i$-th of these lines contains $S$ space-separated integers $NS_1, NS_2, \dots, NS_S$ denoting the number of contestants who solved the $i$-th problem's subtasks.

-----Output-----
Print $P$ lines containing one integer each — the indices of the problems in the increasing order of difficulty.

-----Constraints-----
- $1 \le P \le 100,000$
- $2 \le S \le 30$
- $1 \le SC_i \le 100$ for each valid $i$
- $1 \le NS_i \le 1,000$ for each valid $i$
- in each problem, the scores of all subtasks are unique

-----Subtasks-----
Subtask #1 (25 points): $S = 2$
Subtask #2 (75 points): original constraints

-----Example Input-----
3 3
16 24 60
498 861 589
14 24 62
72 557 819
16 15 69
435 779 232

-----Example Output-----
2
1
3

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible