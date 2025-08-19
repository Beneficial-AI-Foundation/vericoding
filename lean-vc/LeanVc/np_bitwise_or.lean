import Lean

-- Specification for element-wise bitwise OR operation on two arrays
namespace NumpySpecs

def bitwiseOr (a b : Array Int) : Array Int :=
  if a.size = b.size ∧ (∀ i, 0 ≤ i → i < a.size → 0 ≤ a[i] ∧ a[i] ≤ 65535 ∧ 0 ≤ b[i] ∧ b[i] ≤ 65535) then
    a.zipWith b (fun x y => x ||| y)
  else
    Array.empty

-- The specification as a theorem
@[spec]
theorem bitwiseOr_spec (a b : Array Int) :
  a.size = b.size →
  (∀ i, 0 ≤ i → i < a.size → 0 ≤ a[i] ∧ a[i] ≤ 65535 ∧ 0 ≤ b[i] ∧ b[i] ≤ 65535) →
  let res := bitwiseOr a b
  res.size = a.size ∧
  (∀ i, 0 ≤ i → i < a.size → res[i] = a[i] ||| b[i]) :=
  by
    intro h₁ h₂
    simp [bitwiseOr]
    constructor
    · exact Array.size_zipWith _ _ _ h₁
    · intro i h₃ h₄
      simp [Array.zipWith]
      exact rfl
end NumpySpecs
