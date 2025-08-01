/-
# NumPy Convolve Specification

Port of np_convolve.dfy to Lean 4
-/

namespace DafnySpecs.NpConvolve

-- LLM HELPER
def get_at_index (arr : List Float) (i : Int) : Float :=
  if i < 0 ∨ i >= arr.length then 0.0 else arr.get! i.natAbs

/-- Convolution sum helper function -/
def convolutionSum (arr1 arr2 : List Float) (n : Nat) : Float := 
  let indices := List.range arr2.length
  (indices.map (fun k => 
    let i := (n : Int) - (k : Int)
    (get_at_index arr1 i) * (arr2.get! k)
  )).sum

/-- Convolve two sequences -/
def convolve (arr1 arr2 : List Float) : List Float := 
  if arr1.length = 0 ∨ arr2.length = 0 then []
  else
    let result_length := arr1.length + arr2.length - 1
    List.range result_length |>.map (fun n => convolutionSum arr1 arr2 n)

-- LLM HELPER
theorem convolve_nonempty (arr1 arr2 : List Float) 
  (h1 : arr1.length > 0) (h2 : arr2.length > 0) : 
  arr1.length ≠ 0 ∧ arr2.length ≠ 0 := by
  constructor
  · omega
  · omega

/-- Specification: The result has correct length -/
theorem convolve_length (arr1 arr2 : List Float)
  (h1 : arr1.length > 0)
  (h2 : arr2.length > 0) :
  let result := convolve arr1 arr2
  result.length = arr1.length + arr2.length - 1 := by
  unfold convolve
  have h : arr1.length ≠ 0 ∧ arr2.length ≠ 0 := convolve_nonempty arr1 arr2 h1 h2
  simp [h.1, h.2]
  simp [List.length_map, List.length_range]

end DafnySpecs.NpConvolve