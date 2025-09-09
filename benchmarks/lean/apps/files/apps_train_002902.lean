-- <vc-helpers>
-- </vc-helpers>

def sum_of_n (n : Int) : List Int := sorry

theorem sum_of_n_length (n : Int) : (sum_of_n n).length = Int.natAbs n + 1 := sorry

theorem sum_of_n_first_element (n : Int) : 
  (sum_of_n n).get! 0 = 0 := sorry

theorem sum_of_n_consecutive_diffs (n : Int) (i : Nat) 
  (h : i + 1 < (sum_of_n n).length) :
  (sum_of_n n).get! (i + 1) - (sum_of_n n).get! i = 
    if n < 0 
    then (-1 : Int) * (i + 1) 
    else i + 1 := sorry

theorem sum_of_n_signs (n : Int) (i : Nat) 
  (h1 : n ≠ 0)
  (h2 : i > 0) 
  (h3 : i < (sum_of_n n).length) :
  if n < 0 
  then (sum_of_n n).get! i ≤ 0
  else (sum_of_n n).get! i ≥ 0 := sorry

theorem sum_of_n_zero : 
  sum_of_n 0 = [0] := sorry

/-
info: [0, 1, 3, 6]
-/
-- #guard_msgs in
-- #eval sum_of_n 3

/-
info: [0, -1, -3, -6, -10]
-/
-- #guard_msgs in
-- #eval sum_of_n -4

/-
info: [0]
-/
-- #guard_msgs in
-- #eval sum_of_n 0

-- Apps difficulty: introductory
-- Assurance level: unguarded