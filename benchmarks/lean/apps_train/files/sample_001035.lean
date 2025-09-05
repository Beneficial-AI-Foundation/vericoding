Ada's classroom contains $N \cdot M$ tables distributed in a grid with $N$ rows and $M$ columns. Each table is occupied by exactly one student.
Before starting the class, the teacher decided to shuffle the students a bit. After the shuffling, each table should be occupied by exactly one student again. In addition, each student should occupy a table that is adjacent to that student's original table, i.e. immediately to the left, right, top or bottom of that table.
Is it possible for the students to shuffle while satisfying all conditions of the teacher?

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains two space-separated integers $N$ and $M$.

-----Output-----
For each test case, print a single line containing the string "YES" if it is possible to satisfy the conditions of the teacher or "NO" otherwise (without quotes).

-----Constraints-----
- $1 \le T \le 5,000$
- $2 \le N, M \le 50$

-----Example Input-----
2
3 3
4 4

-----Example Output-----
NO
YES

-----Explanation-----
Example case 2: The arrows in the following image depict how the students moved.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
