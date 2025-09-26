-- <vc-preamble>
def find_min_m (arr : List Int) (n : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countUnique (arr : List Int) : Nat :=
  (arr.eraseDups).length
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_m_bounds (arr : List Int) (n : Nat) (h : n = arr.length) :
  1 ≤ find_min_m arr n ∧ find_min_m arr n ≤ countUnique arr := by
  sorry

theorem find_min_m_single_element (arr : List Int) (h : arr.length = 1) :
  find_min_m arr arr.length = 1 := by
  sorry

theorem find_min_m_sorted (arr : List Int) (h : arr.length ≥ 2) :
  find_min_m (List.mergeSort (·≤·) arr) arr.length = 1 := by
  sorry

theorem find_min_m_reverse_sorted (arr : List Int) (h : arr.length ≥ 2) :
  find_min_m (List.mergeSort (·≥·) arr) arr.length = countUnique arr := by
  sorry

theorem find_min_m_small_range (arr : List Int) 
  (h₁ : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 3)
  (h₂ : arr.length ≥ 1)
  (h₃ : arr.length ≤ 10) :
  1 ≤ find_min_m arr arr.length ∧ find_min_m arr arr.length ≤ countUnique arr := by
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_min_m [2, 1] 2

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_min_m [1, 2] 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_min_m [1, 3, 2, 1, 2] 5
-- </vc-theorems>