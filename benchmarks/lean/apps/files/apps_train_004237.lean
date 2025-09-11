-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lamps (a: List Nat) : Nat := sorry

theorem lamps_result_bounded (a: List Nat) : 
  lamps a ≤ a.length ∧ 0 ≤ lamps a := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lamps_alternating_sequence (a: List Nat) (h: a.length > 0) :
  lamps ((List.range a.length).map (fun i => i % 2)) = 0 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval lamps [1, 0, 0, 1, 1, 1, 0]

/-
info: 0
-/
-- #guard_msgs in
-- #eval lamps [1, 0, 1]

/-
info: 5
-/
-- #guard_msgs in
-- #eval lamps [1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible