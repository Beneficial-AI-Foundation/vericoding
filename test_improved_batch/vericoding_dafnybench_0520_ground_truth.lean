/-
  Port of vericoding_dafnybench_0520_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def CountNonEmptySubstrings (s : String) : Int :=
  sorry  -- TODO: implement function body

theorem CountNonEmptySubstrings_spec (s : String) (count : Int) :=
  : count ≥ 0 ∧ count == (|s| * (|s| + 1)) / 2 // Formula for the number of non-empty substrings of a String
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks