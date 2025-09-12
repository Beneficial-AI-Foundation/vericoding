/-
  Port of Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny1_ListContents_SkipHead.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SkipHead  : Node?<T> :=
  sorry  -- TODO: implement function body

theorem SkipHead_spec (r : Node?<T>) :=
  (h_0 : Valid())
  : r == null → |List| == 1 ∧ r ≠ null → r.Valid() ∧ r.List == List[1..] ∧ r.Repr ≤ Repr
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks