/-
  Port of dafny-exercises_tmp_tmp5mvrowrx_paper_krml190_Prepend.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Valid  : Bool :=
  sorry  -- TODO: implement complex function body

def Prepend (d : Data) : Node :=
  sorry  -- TODO: implement function body

theorem Prepend_spec (d : Data) (r : Node) :=
  (h_0 : Valid())
  : r.Valid() ∧ fresh(r.footprint - old(footprint)) ∧ r.list == [d] + list
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks