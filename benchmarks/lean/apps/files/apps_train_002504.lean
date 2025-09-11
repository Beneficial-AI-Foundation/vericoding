-- <vc-preamble>
def List.product : List (List α) → List (List α)
  | [] => [[]]
  | (h :: t) => sorry

def sum [Add α] (l : List α) : α :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_modular_sum (m : Nat) (lists : List (List Int)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_max_modular_sum_bounds (m : Nat) (lists : List (List Int)) 
    (h1 : m > 0) (h2 : lists ≠ []) 
    (h3 : ∀ l ∈ lists, l ≠ []) : 
  let result := find_max_modular_sum m lists
  0 ≤ result ∧ result < m := by
  sorry

theorem find_max_modular_sum_matches_some_combo (m : Nat) (lists : List (List Int))
    (h1 : m > 0) (h2 : lists ≠ []) 
    (h3 : ∀ l ∈ lists, l ≠ []) :
  let result := find_max_modular_sum m lists
  ∃ combo ∈ List.product lists,
    sum (combo.map (λ x => x * x)) % m = result := by
  sorry

theorem find_max_modular_sum_mod_one (lists : List (List Int))
    (h1 : lists ≠ [])
    (h2 : ∀ l ∈ lists, l ≠ []) :
  find_max_modular_sum 1 lists = 0 := by
  sorry

theorem find_max_modular_sum_zeros (m : Nat) (lists : List (List Int))
    (h1 : m > 1)
    (h2 : lists ≠ [])
    (h3 : ∀ l ∈ lists, l ≠ [])
    (h4 : ∀ l ∈ lists, ∀ x ∈ l, x = 0) :
  find_max_modular_sum m lists = 0 := by
  sorry

/-
info: 206
-/
-- #guard_msgs in
-- #eval find_max_modular_sum 1000 [[5, 4], [7, 8, 9], [5, 7, 8, 9, 10]]

/-
info: 20
-/
-- #guard_msgs in
-- #eval find_max_modular_sum 100 [[1, 2], [3, 4]]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded