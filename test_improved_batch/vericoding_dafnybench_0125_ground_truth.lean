/-
  Port of vericoding_dafnybench_0125_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def getAdj (v : T) : set :=
  sorry  -- TODO: implement complex function body


  (h_0 : v !in V)
  : E == old(E) ∧ V == old(V) + {v}
  := by
  sorry  -- TODO: implement proof


  (h_0 : u in V ∧ v in V ∧ (u, v) !in E ∧ u ≠ v)
  : V == old(V) ∧ E == old(E) + {(u, v)}
  := by
  sorry  -- TODO: implement proof


  (h_0 : v in V)
  : V == old(V) - {v} ∧ E == set e | e in old(E) ∧ e.0 ≠ v ∧ e.1 ≠ v
  := by
  sorry  -- TODO: implement proof


  (h_0 : v in C ∧ C ≤ V)
  : V == old(V) - C + {v} ∧ E == set e | e in old(E) ∧ (e.0 !in C ∨ e.1 !in C) ::
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks