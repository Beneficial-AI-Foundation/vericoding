-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ride (s1 s2 : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ride_reflexive {s1 : String} :
  ride s1 s1 = "GO" := by
  sorry

theorem ride_symmetric {s1 s2 : String} :  
  ride s1 s2 = ride s2 s1 := by
  sorry

theorem ride_transitive {s1 s2 s3 : String} :
  ride s1 s2 = "GO" → ride s2 s3 = "GO" → ride s1 s3 = "GO" := by
  sorry

theorem ride_output_format {s1 s2 : String} :
  ride s1 s2 = "GO" ∨ ride s1 s2 = "STAY" := by
  sorry
-- </vc-theorems>