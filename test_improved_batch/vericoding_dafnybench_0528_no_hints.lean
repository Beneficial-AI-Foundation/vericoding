/-
  Port of vericoding_dafnybench_0528_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def DogYears (humanYears : Int) : Int :=
  sorry  -- TODO: implement function body

theorem DogYears_spec (humanYears : Int) (dogYears : Int) :=
  (h_0 : humanYears ≥ 0)
  : dogYears == 7 * humanYears
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks