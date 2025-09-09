def get_average (marks: List Nat) : Nat := sorry

def list_maximum (l: List Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def list_minimum (l: List Nat) : Nat := sorry
def list_sum (l: List Nat) : Nat := sorry

theorem average_in_bounds {marks: List Nat} (h: marks ≠ []) : 
  let avg := get_average marks
  avg ≤ list_maximum marks ∧ avg ≥ list_minimum marks := sorry

theorem average_equals_div_sum {marks: List Nat} (h: marks ≠ []) :
  get_average marks = list_sum marks / marks.length := sorry

theorem empty_list_error : 
  get_average [] = get_average [] → False := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval get_average [2, 2, 2, 2]

/-
info: 25
-/
-- #guard_msgs in
-- #eval get_average [1, 5, 87, 45, 8, 8]

/-
info: 11
-/
-- #guard_msgs in
-- #eval get_average [2, 5, 13, 20, 16, 16, 10]

-- Apps difficulty: introductory
-- Assurance level: guarded