Ram and Shyam are sitting next to each other, hoping to cheat on an exam. However, the examination board has prepared $p$ different sets of questions (numbered $0$ through $p-1$), which will be distributed to the students in the following way:
- The students are assigned roll numbers — pairwise distinct positive integers.
- If a student's roll number is $r$, this student gets the $((r-1)\%p)$-th set of questions.
Obviously, Ram and Shyam can cheat only if they get the same set of questions.
You are given the roll numbers of Ram and Shyam: $A$ and $B$ respectively. Find the number of values of $p$ for which they can cheat, or determine that there is an infinite number of such values.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains two space-separated integers $A$ and $B$.

-----Output-----
For each test case, print a single line — the number of values of $p$ for which Ram and Shyam can cheat, or $-1$ if there is an infinite number of such values.

-----Constraints-----
- $1 \le T \le 100$
- $1 \le A, B \le 10^8$

-----Example Input-----
1
2 6

-----Example Output-----
3

-----Explanation-----
Example case 1: They can cheat for $p = 1$, $p = 2$ or $p = 4$.

def solve_cheat_possibilities (a b : Nat) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
