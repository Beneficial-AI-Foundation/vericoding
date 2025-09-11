-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxJumps (arr : List Int) (d : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxJumps_result_bounded {arr : List Int} {d : Nat}
  (h1 : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 100000)
  (h2 : List.length arr ≤ 100)
  (h3 : 1 ≤ d ∧ d ≤ 100) :
  1 ≤ maxJumps arr d ∧ maxJumps arr d ≤ List.length arr :=
  sorry

theorem maxJumps_zero_d {arr : List Int}
  (h1 : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 100000)
  (h2 : List.length arr ≤ 100) :
  maxJumps arr 0 = 1 :=
  sorry

theorem maxJumps_same_elements {arr : List Int} {n : Nat}
  (h1 : arr = List.replicate n 5)
  (h2 : List.length arr ≤ 100) :
  maxJumps arr (List.length arr) = 1 :=
  sorry

theorem maxJumps_single_element :
  maxJumps [1] 1 = 1 :=
  sorry

theorem maxJumps_two_elements :
  maxJumps [1, 2] 1 = 2 :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval maxJumps [6, 4, 14, 6, 8, 13, 9, 7, 10, 6, 12] 2

/-
info: 1
-/
-- #guard_msgs in
-- #eval maxJumps [3, 3, 3, 3, 3] 3

/-
info: 7
-/
-- #guard_msgs in
-- #eval maxJumps [7, 6, 5, 4, 3, 2, 1] 1
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded