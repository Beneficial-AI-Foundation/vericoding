-- <vc-preamble>
def total_money (s : Student) : Nat :=
  s.fives * 5 + s.tens * 10 + s.twenties * 20

def most_money (students : List Student) : String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_student (students : List Student) : Student :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem most_money_valid_result {students : List Student} (h : students ≠ []) :
  let result := most_money students
  (students.length = 1 → result = (students.head h).name) ∧
  (students.length > 1 → result = "all" ∨ ∃ s ∈ students, result = s.name) :=
sorry

theorem all_equal_returns_all {students : List Student} (h1 : students ≠ []) 
  (h2 : ∀ s ∈ students, total_money s = total_money (students.head h1)) :
  most_money students = "all" :=
sorry

theorem highest_total_wins {students : List Student} (h : students ≠ []) :
  let result := most_money students
  let max_student := find_max_student students
  result ≠ "all" → result = max_student.name :=
sorry

/-
info: 'Phil'
-/
-- #guard_msgs in
-- #eval most_money [phil]

/-
info: 'Phil'
-/
-- #guard_msgs in
-- #eval most_money [cameron, geoff, phil]

/-
info: 'all'
-/
-- #guard_msgs in
-- #eval most_money [andy, stephen, eric]
-- </vc-theorems>