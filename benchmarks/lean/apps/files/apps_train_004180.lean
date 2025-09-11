-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_missing_number (nums : List Nat) : Nat := sorry

theorem find_missing_number_sequence (n : Nat) (h : 0 < n) (h2 : n ≤ 1000) : 
  let nums := (List.range n).map (· + 1)
  let nums_without_last := nums.dropLast
  find_missing_number nums_without_last = n := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 2
-/
-- #guard_msgs in
-- #eval find_missing_number [1, 3, 4]

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_missing_number [1, 2, 3]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_missing_number [2, 3, 4]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded