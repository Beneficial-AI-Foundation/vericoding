def problem_spec
(implementation: Rat → Rat → Rat)
(a h: Rat) :=
let spec (result: Rat) :=
  a = (0 : Rat) → result = (0 : Rat) ∧
  (a ≠ (0 : Rat) → (2 * result) / a = h);
∃ result, implementation a h = result ∧
spec result

def implementation (a h: Rat) : Rat := 
  if a = 0 then 0 else (a * h) / 2

theorem correctness
(a h : Rat)
: problem_spec implementation a h := by
  use implementation a h
  constructor
  · rfl
  · constructor
    · intro ha_zero
      simp [implementation, ha_zero]
    · intro ha_nonzero
      simp [implementation, ha_nonzero]
      field_simp [ha_nonzero]
      ring