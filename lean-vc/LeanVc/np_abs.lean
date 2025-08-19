import Lean

-- Specification for the absolute value function on arrays
namespace NumpySpecs

def abs (a : Array Int) : Array Int :=
  a.map (fun x => Int.natAbs x)

-- The specification as a theorem
theorem abs_spec (a : Array Int) :
  let res := abs a
  res.size = a.size ∧
  (∀ i, 0 ≤ i → i < a.size → res[i] = Int.natAbs a[i]) ∧
  (∀ i, 0 ≤ i → i < a.size → res[i] ≥ 0) :=
  by
    simp [abs]
    constructor
    · exact Array.size_map _ _
    · constructor
      · intro i h₁ h₂
        simp [Array.map]
        exact rfl
      · intro i h₁ h₂
        simp [Array.map]
        apply Int.natAbs_nonneg
end NumpySpecs
