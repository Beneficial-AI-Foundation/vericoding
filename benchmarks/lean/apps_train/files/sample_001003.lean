A manufacturing project consists of exactly $K$ tasks. The board overviewing the project wants to hire $K$ teams of workers — one for each task. All teams begin working simultaneously.
Obviously, there must be at least one person in each team. For a team of $A$ workers, it takes exactly $A$ days to complete the task they are hired for. Each team acts independently, unaware of the status of other teams (whether they have completed their tasks or not), and submits their result for approval on the $A$-th day.
However, the board approves the project only if all $K$ teams complete their tasks on the same day — it rejects everything submitted on any other day. The day after a team finds out that its result was rejected, it resumes work on the same task afresh. Therefore, as long as a team of $A$ workers keeps getting rejected, it submits a new result of their task for approval on the $A$-th, $2A$-th, $3A$-th day etc.
The board wants to hire workers in such a way that it takes exactly $X$ days to complete the project. Find the smallest number of workers it needs to hire.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains two space-separated integers $K$ and $X$.

-----Output-----
For each test case, print a single line containing one integer — the smallest required number of workers.

-----Constraints-----
- $1 \le T \le 40$
- $2 \le K, X \le 10^6$

-----Example Input-----
2
2 3
2 6

-----Example Output-----
4
5

-----Explanation-----
Example case 1: We can hire a team of $3$ workers for task $1$ and $1$ worker for task $2$. The one-man team working on task $2$ completes it and submits the result for approval on each day, but it is rejected on the first and second day. On the third day, the team working on task $1$ also completes their task, so the project gets approved after exactly $3$ days.
Example case 2: We can hire a team of $3$ workers for task $1$ and a team of $2$ workers for task $2$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded