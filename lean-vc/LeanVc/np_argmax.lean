import Lean

-- Specification for finding the index of the maximum value in an array
namespace NumpySpecs

def argmax (arr : Array Float) : Nat :=
  if arr.size > 0 then
    arr.foldl (fun (maxIdx, maxVal) (idx, val) =>
      if val > maxVal then (idx, val) else (maxIdx, maxVal)) (0, arr[0]).fst
  else
    0

-- The specification as a theorem
@[spec]
theorem argmax_spec (arr : Array Float) :
  arr.size > 0 →
  let ret := argmax arr
  ret < arr.size ∧
  (∀ i, 0 ≤ i → i < ret → arr[ret] > arr[i]) ∧
  (∀ i, ret < i → i < arr.size → arr[ret] ≥ arr[i]) :=
  by
    intro h
    simp [argmax]
    constructor
    · exact Nat.lt_of_le_of_lt (Nat.zero_le _) (Array.size_pos _ h)
    · constructor
      · intro i h₁ h₂
        simp [Array.foldl]
        exact rfl
      · intro i h₃ h₄
        simp [Array.foldl]
        exact rfl
end NumpySpecs
