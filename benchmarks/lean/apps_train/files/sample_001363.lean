The auditorium of Stanford University is made up of L*R matrix (assume each coordinate has a chair). On the occasion of an event Chef was called as a chief guest. The auditorium was filled with males (M) and females (F), occupying one chair each. Our Chef is very curious guy, so he asks the gatekeeper some queries. The queries were as follows: Is there any K*K sub-matrix in the auditorium which contains all Males or Females.

-----Input-----
- The first line contains three space-separated integers L, R  and Q describing the dimension of the auditorium and the number of questions Chef will ask.
- Each of next L lines contains R characters (M or F).
- Next Q lines contains K and a character (M or F).

-----Output-----
- For each query output "yes" (without quotes) if there exist any K*K sub-matrix in the auditorium which contains all Males (if he asks about Male) or Females (if he asks about Female), otherwise output "no" (without quotes).

-----Constraints and Subtasks-----
- 1 <= L, R, K <= 1000
- 1 <= Q <= 1e6
Subtask 1: 30 points
- 1 <= L, R, Q <= 200
Subtask 2: 70 points
- Original Contraints

-----Example-----
Input:
4 3 3
MMF
MMM
FFM
FFM
2 F
3 M
1 M

Output:
yes
no
yes

def Matrix := List String
def Query := Nat × Char

def Result := String

def check_matrix_exists (L R : Nat) (matrix : Matrix) (queries : List Query) : List Result :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded