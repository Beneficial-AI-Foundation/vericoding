-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
theorem operation_type_nonempty {sequence : List Int} (h : sequence ≠ []) :
  ∃ (result : Int), operation sequence = result :=
  sorry

theorem operation_empty_case :
  operation [] = 0 :=
  operation_empty operation

theorem operation_type_bounded_length {sequence : List Int} (h : sequence.length ≤ 100) :
  ∃ (result : Int), operation sequence = result :=
  sorry

theorem operation_type_repeated (x : Int) (length : Nat) (h : 0 < length ∧ length ≤ 10) :
  ∃ (result : Int), operation (List.replicate length x) = result :=
  sorry

theorem operation_type_alternating_signs {sequence : List Int} (h : sequence ≠ []) :
  ∃ (result : Int), operation sequence = result :=
  sorry

theorem operation_type_small_ints {sequence : List Int}
    (h1 : sequence ≠ [])
    (h2 : sequence.length ≤ 10)
    (h3 : ∀ x ∈ sequence, -100 ≤ x ∧ x ≤ 100) :
  ∃ (result : Int), operation sequence = result :=
  sorry

/-
info: -6
-/
-- #guard_msgs in
-- #eval calc [-2, -1, 0, 1, 2]

/-
info: 31
-/
-- #guard_msgs in
-- #eval calc [0, 2, 1, -6, -3, 3]

/-
info: 5
-/
-- #guard_msgs in
-- #eval calc [1, 1, 1, 1, 1]
-- </vc-theorems>