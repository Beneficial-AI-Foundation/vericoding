/-
  Port of Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny1_ListContents_Prepend.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Prepend (d : T) : Node<T> :=
  sorry  -- TODO: implement function body

theorem Prepend_spec (d : T) (r : Node<T>) :=
  (h_0 : Valid())
  : r.Valid() ∧ fresh(r.Repr - old(Repr)) ∧ r.List == [d] + List
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks