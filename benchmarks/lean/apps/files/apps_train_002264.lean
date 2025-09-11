-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_replacements_for_pairs (n : Nat) (k : Nat) (arr : List Nat) : Nat := sorry

theorem optimal_array {n k : Nat}
  (h1 : n > 1)
  (h2 : n % 2 = 0)
  (h3 : k > 0)
  (h4 : k ≤ 50) :
  let arr := List.replicate (n/2) 1 ++ List.replicate (n/2) k
  min_replacements_for_pairs n k arr = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 0
-/
-- #guard_msgs in
-- #eval min_replacements_for_pairs 4 2 [1, 2, 1, 2]

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_replacements_for_pairs 4 3 [1, 2, 2, 1]

/-
info: 4
-/
-- #guard_msgs in
-- #eval min_replacements_for_pairs 8 7 [6, 1, 1, 7, 6, 3, 4, 6]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible