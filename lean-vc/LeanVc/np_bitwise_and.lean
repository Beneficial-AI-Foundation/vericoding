import Lean

-- Specification for element-wise bitwise AND operation on two arrays
namespace NumpySpecs

def bitwiseAnd (a b : Array Int) : Array Int :=
  if a.size = b.size then
    a.zipWith b (fun x y => x &&& y)
  else
    Array.empty

-- The specification as a theorem
theorem bitwiseAnd_spec (a b : Array Int) :
  a.size = b.size →
  let res := bitwiseAnd a b
  res.size = a.size ∧
  (∀ i, 0 ≤ i → i < a.size → res[i] = a[i] &&& b[i]) :=
  by
    intro h
    simp [bitwiseAnd]
    constructor
    · exact Array.size_zipWith _ _ _ h
    · intro i h₁ h₂
      simp [Array.zipWith]
      exact rfl
end NumpySpecs
