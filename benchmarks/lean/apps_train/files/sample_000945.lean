Mr. Pr and Ms. Ad are at $a$ and $b$ respectively on an infinite number line. Mr. Pr wants to meet Ms. Ad.
Mr. Pr can choose to move  $c$ or $d$ units in 1 second. If Mr. Pr moves $c$ units then Ms. Ad will move $d$ units and vice versa. (Both of them always moved in positive x-direction)
You have to determine if Mr. Pr can meet with Ms. Ad after some integral amount of time, given that Mr. Pr chooses optimally. Note that meeting after a fractional amount of time does not count.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains four space separated integers, $a$, $b$, $c$, and $d$.

-----Output:-----
- For each test case, output a single line containing "YES" if Mr. Pr meets with Ms. Ad, otherwise "NO".

-----Constraints-----
- $1 \leq T \leq 10^5$
- $1 \leq a,b,c,d \leq 10^9$

-----Sample Input:-----
2
3 4 1 2
10 20 3 7

-----Sample Output:-----
YES
NO

-----Explanation:-----
In the first test case, Mr. Pr will move 2 units in the first second and Ms. Ad moves 1 unit simultaneously and they meet. 
In the second test case, it is impossible to meet (fractional time is not allowed).

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
