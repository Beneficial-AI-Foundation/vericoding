-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Stick := Nat × Nat

def max_sticks_chopped (sticks : List Stick) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_is_valid_integer (sticks : List Stick) (h : sticks ≠ []) : 
  let result := max_sticks_chopped sticks
  1 ≤ result ∧ result ≤ sticks.length :=
sorry

theorem single_stick_returns_one (pos height : Nat) (h₁ : pos ≥ 1) (h₂ : height ≥ 1) :
  max_sticks_chopped [(pos, height)] = 1 :=
sorry

theorem spreading_sticks_improves_result (sticks : List Stick) (h : sticks.length ≥ 2) :
  let spread_sticks := sticks.enum.map (fun (i, stick) => (i * 100, stick.2))
  max_sticks_chopped spread_sticks ≥ max_sticks_chopped sticks :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval max_sticks_chopped [(1, 2), (2, 1), (5, 10), (10, 9), (19, 1)]

/-
info: 4
-/
-- #guard_msgs in
-- #eval max_sticks_chopped [(1, 2), (2, 1), (5, 10), (10, 9), (20, 1)]

/-
info: 1
-/
-- #guard_msgs in
-- #eval max_sticks_chopped [(1, 2)]
-- </vc-theorems>