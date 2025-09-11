-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_transform (arr : List Int) : String := sorry

theorem sort_transform_output_length 
  {arr : List Int}
  (h1 : arr.length ≥ 4)
  (h2 : arr.length ≤ 20) 
  (h3 : ∀ x ∈ arr, x ≥ 33 ∧ x ≤ 126)
  (h4 : arr.Nodup) :
  (sort_transform arr).length = 19 := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 'oprn-nors-sron-nors'
-/
-- #guard_msgs in
-- #eval sort_transform [111, 112, 113, 114, 115, 113, 114, 110]

/-
info: '3>c~-3>d~-~d>3-3>d~'
-/
-- #guard_msgs in
-- #eval sort_transform [51, 62, 73, 84, 95, 100, 99, 126]

/-
info: 'Beoq-7Boq-qoB7-7Boq'
-/
-- #guard_msgs in
-- #eval sort_transform [66, 101, 55, 111, 113]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded