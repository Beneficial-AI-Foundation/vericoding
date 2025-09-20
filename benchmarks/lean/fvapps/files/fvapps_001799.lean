-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pour_water (heights : List Nat) (V : Nat) (K : Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pour_water_result_length {heights : List Nat} {V K : Nat} 
  (h : K < heights.length) :
  (pour_water heights V K).length = heights.length :=
  sorry

theorem pour_water_total_water_added {heights : List Nat} {V K : Nat}
  (h : K < heights.length) :
  (pour_water heights V K).foldl (· + ·) 0 - heights.foldl (· + ·) 0 = V :=
  sorry

theorem pour_water_heights_never_decrease {heights : List Nat} {V K : Nat}
  (h : K < heights.length) :
  List.zip (pour_water heights V K) heights
  |>.all (fun p => p.1 ≥ p.2) := 
  sorry

theorem pour_water_water_trapped {heights : List Nat} {V K : Nat} 
  (h : K < heights.length)
  (i : Nat)
  (hi : i > 0 ∧ i < (heights.length - 1))
  (hw : (pour_water heights V K).get ⟨i, sorry⟩ > heights.get ⟨i, sorry⟩) :
  ((pour_water heights V K).get ⟨i-1, sorry⟩ ≥ (pour_water heights V K).get ⟨i, sorry⟩) ∨
  ((pour_water heights V K).get ⟨i+1, sorry⟩ ≥ (pour_water heights V K).get ⟨i, sorry⟩) :=
  sorry
-- </vc-theorems>