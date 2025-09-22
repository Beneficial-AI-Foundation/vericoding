-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def avgArray (arrays : List (List Int)) : List Float := sorry

theorem avg_array_length_preserving (arrays : List (List Int)) 
  (h1 : arrays.length > 0) (h2 : ∀ arr ∈ arrays, arr.length = arrays[0]!.length) :
  (avgArray arrays).length = arrays[0]!.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem avg_array_result_within_bounds (arrays : List (List Int)) (i : Nat)
  (h1 : arrays.length > 0) 
  (h2 : ∀ arr ∈ arrays, arr.length = arrays[0]!.length)
  (h3 : i < arrays[0]!.length) :
  let col := arrays.map (λ arr => arr[i]!)
  let result := avgArray arrays
  let colMin := Float.ofInt (col.foldl min col[0]!)
  let colMax := Float.ofInt (col.foldl max col[0]!)
  result[i]! ≥ colMin ∧ result[i]! ≤ colMax := sorry

theorem avg_array_singleton (arr : List Int) :
  avgArray [arr] = arr.map Float.ofInt := sorry

theorem avg_array_non_negative (arrays : List (List Int))
  (h1 : arrays.length > 0)
  (h2 : ∀ arr ∈ arrays, arr.length = arrays[0]!.length)
  (h3 : ∀ arr ∈ arrays, ∀ x ∈ arr, x ≥ 0) :
  ∀ x ∈ avgArray arrays, x ≥ 0 := sorry
-- </vc-theorems>