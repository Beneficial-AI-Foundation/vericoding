/-
  Port of vericoding_dafnybench_0717_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  (h_0 : valid())
  (h_1 : putEnabled(p)          //  |buffer| < maxBufferSize)
  := by
  sorry  -- TODO: implement proof


  (h_0 : getEnabled(p))
  (h_1 : valid()                //  Invariant is inductive)
  : |buffer| == |old(buffer)| - 1   //  this invariant is not needed and can be omitted
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks