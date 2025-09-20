-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def elements_sum (arr : List (List Int)) (default : Int := 0) : Int := sorry

theorem elements_sum_with_default 
  (arr : List (List Int)) (default : Int) :
  elements_sum arr default = 
  let reversed := arr.reverse
  (List.range reversed.length).foldl
    (fun sum i => sum + 
      match reversed.get? i with
      | some row => match row.get? i with
                   | some x => x
                   | none => default
      | none => default) 0
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem elements_sum_type (arr : List (List Int)) :
  ∃ (n : Int), elements_sum arr = n := sorry

theorem elements_sum_nonempty
  (arr : List (List Int))
  (h : ∀ l ∈ arr, l.length > 0) :
  elements_sum arr = 
  let reversed := arr.reverse
  (List.range reversed.length).foldl
    (fun sum i => sum + 
      match reversed.get? i with
      | some row => match row.get? i with
                   | some x => x
                   | none => 0
      | none => 0) 0
  := sorry
-- </vc-theorems>