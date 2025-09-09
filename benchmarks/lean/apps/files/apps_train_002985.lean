-- <vc-helpers>
-- </vc-helpers>

def index (arr : List Int) (n : Nat) : Int := sorry

theorem index_valid_index {arr : List Int} {n : Nat} (h : n < arr.length) :
  index arr n = (arr.get ⟨n, h⟩) ^ n := sorry

theorem index_invalid_index {arr : List Int} {n : Nat} (h : n ≥ arr.length) :
  index arr n = -1 := sorry

theorem index_empty_array {n : Nat} :
  index [] n = -1 := sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval index [1, 2, 3, 4] 2

/-
info: 1000000
-/
-- #guard_msgs in
-- #eval index [1, 3, 10, 100] 3

/-
info: -1
-/
-- #guard_msgs in
-- #eval index [1, 2] 3

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible