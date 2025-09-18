-- <vc-preamble>
def abs (x : Int) : Int := 
  if x < 0 then -x else x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (arr : List Int) : Int := sorry

theorem solve_sequence_with_small_deviations {arr : List Int} 
  (h1 : arr.length ≥ 3) (h2 : arr.length ≤ 10)
  (h3 : ∃ start step : Int, ∀ (i : Fin arr.length), 
    abs (arr.get i - (start + i.val * step)) ≤ 1) :
  let result := solve arr
  result ≥ 0 ∧ 
  result ≤ (List.range (arr.length-1)).foldl 
    (fun acc i => acc + abs (arr.get ⟨i+1, sorry⟩ - arr.get ⟨i, sorry⟩)) 0 := 
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_arbitrary_sequences {arr : List Int}
  (h1 : arr.length ≥ 3) (h2 : arr.length ≤ 10)
  (h3 : ∀ x ∈ arr, -100 ≤ x ∧ x ≤ 100) :
  let result := solve arr
  result ≥ -1 ∧ 
  (result ≠ -1 → result ≥ 0) := 
sorry

theorem solve_minimum_length_sequence {arr : List Int}
  (h : arr.length = 3) :
  let result := solve arr
  result ≠ -1 → 
  result ≤ abs (arr.get ⟨1, sorry⟩ - arr.get ⟨0, sorry⟩) + 
           abs (arr.get ⟨2, sorry⟩ - arr.get ⟨1, sorry⟩) :=
sorry

theorem solve_constant_sequence {arr : List Int}
  (h1 : arr.length ≥ 3) (h2 : arr.length ≤ 10)
  (h3 : ∀ (i j : Fin arr.length), arr.get i = arr.get j) :
  solve arr = 0 :=
sorry
-- </vc-theorems>