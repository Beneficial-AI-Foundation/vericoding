-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fibfusc (n : Nat) : Int × Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fibfusc_is_pair : ∀ n : Nat, 
  ∃ x y : Int, fibfusc n = (x, y) := by sorry

theorem fibfusc_base_cases : 
  (fibfusc 0 = (1, 0)) ∧ 
  (fibfusc 1 = (0, 1)) ∧ 
  (fibfusc 2 = (-1, 1)) ∧
  (fibfusc 3 = (-3, 5)) ∧ 
  (fibfusc 4 = (-7, 13)) := by sorry

theorem fibfusc_growth : ∀ n : Nat,
  n > 4 → (let (_, y) := fibfusc n; y > 13 ∨ y < -13) := by sorry
-- </vc-theorems>