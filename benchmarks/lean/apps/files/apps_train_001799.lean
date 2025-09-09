-- <vc-helpers>
-- </vc-helpers>

def pour_water (heights : List Nat) (V : Nat) (K : Nat) : List Nat :=
  sorry

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

/-
info: [2, 2, 2, 3, 2, 2, 2]
-/
-- #guard_msgs in
-- #eval pour_water [2, 1, 1, 2, 1, 2, 2] 4 3

/-
info: [2, 3, 3, 4]
-/
-- #guard_msgs in
-- #eval pour_water [1, 2, 3, 4] 2 2

/-
info: [4, 4, 4]
-/
-- #guard_msgs in
-- #eval pour_water [3, 1, 3] 5 1

-- Apps difficulty: interview
-- Assurance level: unguarded