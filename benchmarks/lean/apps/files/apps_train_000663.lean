-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (seq : List Nat) : Nat × Nat := sorry

def isValidAfterReverse (seq : List Nat) (l r : Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_sorted_sequence {n : Nat} (h : n > 0) :
  let seq := List.range' 1 n
  solve n seq = (0, 0) := sorry

theorem solve_reversed_sequence {n : Nat} (h : n > 1) :
  let seq := List.reverse (List.range' 1 n) 
  solve n seq = (1, n) := sorry

/-
info: (2, 6)
-/
-- #guard_msgs in
-- #eval solve 8 [1, 6, 5, 4, 3, 2, 7, 8]

/-
info: (0, 0)
-/
-- #guard_msgs in
-- #eval solve 4 [1, 2, 3, 4]

/-
info: (1, 3)
-/
-- #guard_msgs in
-- #eval solve 3 [3, 2, 1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible