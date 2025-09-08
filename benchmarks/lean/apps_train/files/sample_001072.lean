/-
There were $N$ students (numbered $1$ through $N$) participating in the Indian Programming Camp (IPC) and they watched a total of $K$ lectures (numbered $1$ through $K$). For each student $i$ and each lecture $j$, the $i$-th student watched the $j$-th lecture for $T_{i, j}$ minutes.
Additionally, for each student $i$, we know that this student asked the question, "What is the criteria for getting a certificate?" $Q_i$ times.
The criteria for getting a certificate is that a student must have watched at least $M$ minutes of lectures in total and they must have asked the question no more than $10$ times.
Find out how many participants are eligible for a certificate.

-----Input-----
- The first line of the input contains three space-separated integers $N$, $M$ and $K$.
- $N$ lines follow. For each valid $i$, the $i$-th of these lines contains $K+1$ space-separated integers $T_{i, 1}, T_{i, 2}, \ldots, T_{i, K}, Q_i$.

-----Output-----
Print a single line containing one integer — the number of participants eligible for a certificate. 

-----Constraints-----
- $1 \le N, K \le 1,000$
- $1 \le M \le 10^6$
- $1 \le Q_i \le 10^6$ for each valid $i$
- $1 \le T_{i, j} \le 1,000$ for each valid $i$ and $j$

-----Example Input-----
4 8 4
1 2 1 2 5
3 5 1 3 4
1 2 4 5 11
1 1 1 3 12

-----Example Output-----
1

-----Explanation-----
- Participant $1$ watched $1 + 2 + 1 + 2 = 6$ minutes of lectures and asked the question $5$ times. Since $6 < M$, this participant does not receive a certificate.
- Participant $2$ watched $3 + 5 + 1 + 3 = 12$ minutes of lectures and asked the question $4$ times. Since $12 \ge M$ and $4 \le 10$, this participant receives a certificate.
- Participant $3$ watched $1 + 2 + 4 + 5 = 12$ minutes of lectures and asked the question $11$ times. Since $12 \ge M$ but $11 > 10$, this participant does not receive a certificate.
- Participant $4$ watched $1 + 1 + 1 + 3 = 6$ minutes of lectures and asked the question $12$ times. Since $6 < M$ and $12 > 10$, this participant does not receive a certificate.
Only participant $2$ receives a certificate.
-/

def List.sum (xs : List Nat) : Nat :=
match xs with
| [] => 0
| x::xs => x + xs.sum

-- <vc-helpers>
-- </vc-helpers>

def count_eligible_students (N M K : Nat) (student_data : List (List Nat)) : Nat :=
sorry

theorem count_eligible_students_empty_data
  {N M K : Nat} (h1 : N ≥ 1) (h2 : M ≥ 1) (h3 : K ≥ 1) :
  count_eligible_students N M K [] = 0 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_eligible_students 4 8 4 [[1, 2, 1, 2, 5], [3, 5, 1, 3, 4], [1, 2, 4, 5, 11], [1, 1, 1, 3, 12]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_eligible_students 2 10 2 [[1, 2, 11], [2, 3, 12]]

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_eligible_students 2 5 2 [[2, 4, 5], [3, 3, 2]]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible