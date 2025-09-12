/-
  Port of vericoding_dafnybench_0630_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

function MinPair(s: seq<int>) : (r: int)
  if s[0]! ≤ s[1]! then s[0]! else s[1]!

function min(s: seq<int>) : (r: int)
  sorry  -- TODO: implement complex function body

def SecondSmallest (s : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem SecondSmallest_spec (s : Array Int) (secondSmallest : Int) :=
  (h_0 : s.size ≥ 2)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks