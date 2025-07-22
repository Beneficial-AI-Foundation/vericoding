/-
# NumPy Convolve Specification

Port of np_convolve.dfy to Lean 4
-/

namespace DafnySpecs.NpConvolve

/-- Convolution sum helper function -/
def convolutionSum (arr1 arr2 : List Float) (n : Nat) : Float := 
  let pairs := List.zip arr1 (arr2.reverse)
  let validPairs := pairs.filter (fun (i, j) => i < arr1.length && j < arr2.length)
  let indices := List.range (min arr1.length arr2.length)
  let sum := indices.foldl (fun acc k => 
    if k < arr1.length && n - k < arr2.length && n >= k then
      acc + arr1[k]! * arr2[n - k]!
    else
      acc
  ) 0.0
  sum

/-- Convolve two sequences -/
def convolve (arr1 arr2 : List Float) : List Float := 
  if arr1.length = 0 || arr2.length = 0 then
    []
  else
    let resultLength := arr1.length + arr2.length - 1
    List.range resultLength |>.map (convolutionSum arr1 arr2)

-- LLM HELPER
lemma List.length_range (n : Nat) : (List.range n).length = n := by
  induction n with
  | zero => simp [List.range]
  | succ n ih => simp [List.range, List.length_cons, ih]

-- LLM HELPER  
lemma List.length_map {α β : Type*} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.map, List.length_cons, ih]

/-- Specification: The result has correct length -/
theorem convolve_length (arr1 arr2 : List Float)
  (h1 : arr1.length > 0)
  (h2 : arr2.length > 0) :
  let result := convolve arr1 arr2
  result.length = arr1.length + arr2.length - 1 := by
  simp [convolve]
  have h1' : arr1.length ≠ 0 := Nat.not_eq_zero_of_zero_lt h1
  have h2' : arr2.length ≠ 0 := Nat.not_eq_zero_of_zero_lt h2
  simp [h1', h2']
  rw [List.length_map, List.length_range]

end DafnySpecs.NpConvolve