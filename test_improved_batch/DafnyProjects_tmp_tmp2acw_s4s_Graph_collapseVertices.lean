/-
  Port of DafnyProjects_tmp_tmp2acw_s4s_Graph_collapseVertices.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def getAdj (v : T) : set :=
  sorry  -- TODO: implement complex function body


  (h_0 : v in C ∧ C ≤ V)
  : V == old(V) - C + {v} ∧ E == set e | e in old(E) ∧ (e.0 !in C ∨ e.1 !in C) ::
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks