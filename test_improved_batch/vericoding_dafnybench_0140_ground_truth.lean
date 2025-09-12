/-
  Port of vericoding_dafnybench_0140_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Get (i : Int) : T :=
  if M ≤ i then front[i - M] else depot.Get(i/256)[i%256]


  (h_0 : Valid() ∧ 0 ≤ i < |Elements|)
  := by
  sorry  -- TODO: implement proof


  (h_0 : Valid())
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks