-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum (xs : List Nat) : Nat := List.foldl (· + ·) 0 xs

def find_max_segment_scores (n m : Nat) (arr : List Nat) : Nat × Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_element {n : Nat} {arr : List Nat}
  (h1 : n > 0)
  (h2 : n ≤ 10)
  (h3 : arr = [n]) :
  find_max_segment_scores 1 (n+1) arr = (n % (n+1), 1) := sorry

/-
info: (2, 1)
-/
-- #guard_msgs in
-- #eval find_max_segment_scores 2 3 [1, 2]

/-
info: (4, 2)
-/
-- #guard_msgs in
-- #eval find_max_segment_scores 3 5 [2, 4, 3]

/-
info: (2, 2)
-/
-- #guard_msgs in
-- #eval find_max_segment_scores 4 3 [1, 2, 3, 4]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible