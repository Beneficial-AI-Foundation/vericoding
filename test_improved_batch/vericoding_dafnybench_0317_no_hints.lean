/-
  Port of vericoding_dafnybench_0317_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  : Contents == old(Contents) + {t}
  := by
  sorry  -- TODO: implement proof

def Retrieve (matchCriterion : Thing -> bool) : Thing :=
  sorry  -- TODO: implement function body

theorem Retrieve_spec (matchCriterion : Thing -> bool) (thing : Thing) :=
  (h_0 : ∃ t, t in Contents ∧ matchCriterion(t))
  : Contents == old(Contents) ∧ thing in Contents ∧ matchCriterion(thing)
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks