-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binary_cleaner (seq : List Int) : List Int × List Nat := sorry

theorem binary_cleaner_properties (seq : List Int) :
  let result := binary_cleaner seq
  (∀ x ∈ result.1, x < 2) ∧
  (∀ i ∈ result.2, i < seq.length) ∧
  (List.all result.2 fun i => seq.get! i ≥ 2) ∧
  result.1.length + result.2.length = seq.length := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: ([0, 1, 1, 0, 1, 1], [2, 5])
-/
-- #guard_msgs in
-- #eval binary_cleaner [0, 1, 2, 1, 0, 2, 1, 1]

/-
info: ([0, 1, 1, 0], [3])
-/
-- #guard_msgs in
-- #eval binary_cleaner [0, 1, 1, 2, 0]

/-
info: ([1], [])
-/
-- #guard_msgs in
-- #eval binary_cleaner [1]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible