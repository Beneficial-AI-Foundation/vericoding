import Lean

-- Specification for element-wise addition of two arrays
namespace NumpySpecs

def add (a b : Array Int) : Array Int :=
  if a.size = b.size then
    Array.zipWith (fun x y => x + y) a b
  else
    Array.empty

-- The specification as a theorem
theorem add_spec (a b : Array Int) :
  a.size = b.size →
  let res := add a b
  res.size = a.size ∧
  (∀ i, 0 ≤ i → i < a.size → res[i] = a[i] + b[i]) :=
  by
    intro h
    simp [add]
    constructor
    · exact Array.size_zipWith _ _ _ h
    · intro i h₁ h₂
      simp [Array.zipWith]
      exact rfl
end NumpySpecs
