-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculateDistinctPlantHeightsAvg (n : Nat) (heights : String) : Float := sorry

theorem avg_between_min_max 
  (n : Nat) (heights : List Nat) (h₁ : ∀ x ∈ heights, 1 ≤ x ∧ x ≤ 1000) (h₂ : heights ≠ []) :
  let result := calculateDistinctPlantHeightsAvg n (heights.toString)
  let min_height := heights.minimum?.get!
  let max_height := heights.maximum?.get!
  Float.ofNat min_height ≤ result ∧ result ≤ Float.ofNat max_height := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem duplicate_heights_same_avg 
  (n : Nat) (heights : List Nat) (h₁ : ∀ x ∈ heights, 1 ≤ x ∧ x ≤ 1000) (h₂ : heights ≠ []) :
  let result₁ := calculateDistinctPlantHeightsAvg n (heights.toString)
  let result₂ := calculateDistinctPlantHeightsAvg (2*n) (heights.toString ++ heights.toString)
  (result₁ - result₂).abs < 0.0001 := sorry

theorem sorted_heights_avg 
  (n : Nat) (heights : List Nat) (h₁ : ∀ x ∈ heights, 1 ≤ x ∧ x ≤ 1000) 
  (h₂ : heights ≠ []) (h₃ : ∀ i j, i < j → j < heights.length → heights[i]! ≤ heights[j]!) :
  let result := calculateDistinctPlantHeightsAvg n (heights.toString)
  let distinct := heights.eraseDups
  let total : Nat := distinct.foldl (init := 0) (·+·)
  let expected := (Float.ofNat total) / (Float.ofNat distinct.length)
  (result - expected).abs < 0.0001 := sorry

theorem single_height (h : 1 ≤ 5 ∧ 5 ≤ 1000) :
  calculateDistinctPlantHeightsAvg 1 "5" = 5.0 := sorry

theorem same_heights (h : 1 ≤ 7 ∧ 7 ≤ 1000) :
  calculateDistinctPlantHeightsAvg 3 "7 7 7" = 7.0 := sorry
-- </vc-theorems>