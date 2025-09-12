/-
  Port of dafny-exercises_tmp_tmp5mvrowrx_paper_krml190_SkipHead.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Valid  : Bool :=
  sorry  -- TODO: implement complex function body

def SkipHead  : Node? :=
  sorry  -- TODO: implement function body

theorem SkipHead_spec (r : Node?) :=
  (h_0 : Valid())
  : r == null → |list| == 1 ∧ r ≠ null → r.Valid() ∧ r.footprint ≤ footprint
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks