def remove_smallest (list : List Int) : List Int :=
  sorry

def minimum (list : List Int) : Option Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def list_eq (l1 l2 : List Int) : Bool :=
  sorry

theorem remove_smallest_length (list : List Int) :
  list = [] → remove_smallest list = [] ∧
  list ≠ [] → List.length (remove_smallest list) = List.length list - 1 :=
sorry

/-
info: [2, 3, 4, 5]
-/
-- #guard_msgs in
-- #eval remove_smallest [1, 2, 3, 4, 5]

/-
info: [2, 2, 2, 1]
-/
-- #guard_msgs in
-- #eval remove_smallest [2, 2, 1, 2, 1]

/-
info: []
-/
-- #guard_msgs in
-- #eval remove_smallest []

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible