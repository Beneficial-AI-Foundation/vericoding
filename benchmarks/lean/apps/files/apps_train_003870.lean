-- <vc-helpers>
-- </vc-helpers>

def first_tooth (lst : List Int) : Int := sorry

theorem first_tooth_output_range {lst : List Int} (h : lst.length ≥ 2) :
  let result := first_tooth lst
  result = -1 ∨ (0 ≤ result ∧ result < lst.length) := sorry

theorem constant_list_gives_negative_one {lst : List Int} (h : lst.length ≥ 2) :
  let val := lst.get ⟨0, sorry⟩
  let constant_list := List.replicate lst.length val
  first_tooth constant_list = -1 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval first_tooth [1, 2, 3, 4]

/-
info: 2
-/
-- #guard_msgs in
-- #eval first_tooth [1, 2, 6, 4]

/-
info: -1
-/
-- #guard_msgs in
-- #eval first_tooth [1, 1, 1, 1]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible