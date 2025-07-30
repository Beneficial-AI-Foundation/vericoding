namespace NpConvolve

-- LLM HELPER
def getAt (arr : List Float) (i : Nat) : Float :=
  arr[i]?.getD 0.0

def convolutionSum (arr1 arr2 : List Float) (n : Nat) : Float :=
  let indices := List.range (n + 1)
  indices.foldl (fun acc k => acc + (getAt arr1 k) * (getAt arr2 (n - k))) 0.0

def convolve (arr1 arr2 : List Float) : List Float :=
  if arr1.length = 0 || arr2.length = 0 then []
  else
    let resultLength := arr1.length + arr2.length - 1
    List.range resultLength |>.map (convolutionSum arr1 arr2)

-- LLM HELPER
theorem list_range_length (n : Nat) : (List.range n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => 
    rw [List.range_succ_last]
    simp [List.length_cons, List.length_append, ih]

-- LLM HELPER
theorem map_length {α β : Type*} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons _ _ ih => simp [ih]

theorem convolve_spec (arr1 arr2 : List Float)
  (h1 : arr1.length > 0)
  (h2 : arr2.length > 0) :
  let result := convolve arr1 arr2
  result.length = arr1.length + arr2.length - 1 := by
  simp [convolve]
  have h1' : arr1.length ≠ 0 := Nat.ne_of_gt h1
  have h2' : arr2.length ≠ 0 := Nat.ne_of_gt h2
  simp [h1', h2']
  rw [map_length, list_range_length]

end NpConvolve