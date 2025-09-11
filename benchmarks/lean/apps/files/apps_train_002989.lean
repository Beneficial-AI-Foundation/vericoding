-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def int_to_word (n : Nat) : String := sorry

def sort_by_name (arr : List Nat) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_by_name_length (arr : List Nat) :
  (sort_by_name arr).length = arr.length := sorry

theorem sort_by_name_permutation (arr : List Nat) :
  ∀ x, x ∈ arr ↔ x ∈ sort_by_name arr := sorry

theorem sort_by_name_idempotent (arr : List Nat) :
  sort_by_name (sort_by_name arr) = sort_by_name arr := sorry

/-
info: [4, 1, 3, 2]
-/
-- #guard_msgs in
-- #eval sort_by_name [1, 2, 3, 4]

/-
info: []
-/
-- #guard_msgs in
-- #eval sort_by_name []

/-
info: [8, 8, 9, 9, 10, 10]
-/
-- #guard_msgs in
-- #eval sort_by_name [8, 8, 9, 9, 10, 10]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible