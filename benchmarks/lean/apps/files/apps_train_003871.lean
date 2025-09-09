-- <vc-helpers>
-- </vc-helpers>

def sequence_classifier (arr : List Int) : Nat :=
  sorry

theorem classifier_output_range {arr : List Int} (h : arr.length ≥ 2) :
  let result := sequence_classifier arr
  0 ≤ result ∧ result ≤ 5 :=
sorry

theorem constant_sequence {arr : List Int} (h : arr.length ≥ 2) :
  let constant_arr := List.replicate arr.length (arr.get ⟨0, sorry⟩)
  sequence_classifier constant_arr = 5 :=
sorry

theorem reverse_properties {arr : List Int} (h : arr.length ≥ 2) :
  let forward := sequence_classifier arr
  let backward := sequence_classifier arr.reverse
  (forward = 1 → backward = 3) ∧
  (forward = 2 → backward = 4) ∧
  (forward = 5 → backward = 5) :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval sequence_classifier [3, 5, 8, 1, 14, 3]

/-
info: 1
-/
-- #guard_msgs in
-- #eval sequence_classifier [3, 5, 8, 9, 14, 23]

/-
info: 5
-/
-- #guard_msgs in
-- #eval sequence_classifier [8, 8, 8, 8, 8, 8]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible