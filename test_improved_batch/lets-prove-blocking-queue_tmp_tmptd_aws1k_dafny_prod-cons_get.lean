/-
  Port of lets-prove-blocking-queue_tmp_tmptd_aws1k_dafny_prod-cons_get.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  (h_0 : getEnabled(p))
  (h_1 : valid()                //  Invariant is inductive)
  : |buffer| == |old(buffer)| - 1   //  this invariant is not needed and can be omitted
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks