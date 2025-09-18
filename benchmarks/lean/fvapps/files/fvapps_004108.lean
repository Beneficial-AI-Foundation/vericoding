-- <vc-preamble>
def sort_number (l : List Int) : List Int := sorry

theorem sort_number_length {l : List Int} (h : l ≠ []) : 
  (sort_number l).length = l.length := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSorted (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!
-- </vc-definitions>

-- <vc-theorems>
theorem sort_number_first {l : List Int} (h : l ≠ []) :
  (sort_number l).head! = 1 := sorry

theorem sort_number_deterministic {l : List Int} (h : l ≠ []) :
  sort_number l = sort_number l := sorry

/-
info: [1, 1, 2, 3, 4]
-/
-- #guard_msgs in
-- #eval sort_number [1, 2, 3, 4, 5]

/-
info: [1, 2, 2]
-/
-- #guard_msgs in
-- #eval sort_number [2, 2, 2]

/-
info: [1]
-/
-- #guard_msgs in
-- #eval sort_number [42]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible