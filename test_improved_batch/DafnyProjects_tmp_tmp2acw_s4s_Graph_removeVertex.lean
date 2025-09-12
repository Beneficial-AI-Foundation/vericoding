/-
  Port of DafnyProjects_tmp_tmp2acw_s4s_Graph_removeVertex.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def getAdj (v : T) : set :=
  sorry  -- TODO: implement complex function body


  (h_0 : v in V)
  : V == old(V) - {v} ∧ E == set e | e in old(E) ∧ e.0 ≠ v ∧ e.1 ≠ v
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks