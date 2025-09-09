-- <vc-helpers>
-- </vc-helpers>

def count_enemies_killed (s : String) : Nat := 
  sorry

theorem count_enemies_killed_equality (s : String) : 
  count_enemies_killed s = (s.toList.filter (fun c => c.isAlpha && c.isUpper)).length := 
  sorry

theorem count_enemies_killed_nonnegative (s : String) : 
  count_enemies_killed s ≥ 0 := 
  sorry

theorem count_enemies_killed_bound (s : String) : 
  count_enemies_killed s ≤ s.length := 
  sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible