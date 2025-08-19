import Lean

-- Specification for generating evenly spaced values within a given interval
namespace NumpySpecs

def arange (start stop step : Float) : Array Float :=
  if step ≠ 0.0 ∧ ((step < 0.0 → start > stop) ∧ (step > 0.0 → start < stop)) then
    let n := Float.floor ((stop - start) / step)
    Array.init n.toNat (fun i => start + step * i.toFloat)
  else
    Array.empty

-- The specification as a theorem
@[spec]
theorem arange_spec (start stop step : Float) :
  step ≠ 0.0 →
  ((step < 0.0 → start > stop) ∧ (step > 0.0 → start < stop)) →
  let ret := arange start stop step
  ret.size = Float.floor ((stop - start) / step).toNat ∧
  ret.size > 0 ∧
  ret[0] = start ∧
  (∀ i, 1 ≤ i → i < ret.size → ret[i] - ret[i - 1] = step) :=
  by
    intro h₁ h₂
    simp [arange]
    constructor
    · exact Array.size_init _
    · constructor
      · exact Nat.pos_of_ne_zero (Float.floor_pos _ _ h₁ h₂)
      · constructor
        · simp [Array.init]
          exact rfl
        · intro i h₃ h₄
          simp [Array.init]
          exact rfl
end NumpySpecs
