/-
  Port of vericoding_dafnybench_0361_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def maxcheck (s : array<nat>) (i : Int) (max : Int) : Int :=
  sorry  -- TODO: implement complex function body

def max (s : array<nat>) : Int :=
  sorry  -- TODO: implement function body

theorem max_spec (s : array<nat>) (a : Int) :=
  (h_0 : s.size > 0)
  : ∀ x :: 0 ≤ x < s.size → a ≥ s[x]! ∧ a in s[..]
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks