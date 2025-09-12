/-
  Port of Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_week10_ExtensibleArray_Add.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Get (i : Int) : T :=
  if M ≤ i then front[i - M] else depot.Get(i/256)[i%256]


  (h_0 : Valid())
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks