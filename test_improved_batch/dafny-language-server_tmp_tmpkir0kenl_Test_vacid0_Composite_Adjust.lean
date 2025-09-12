/-
  Port of dafny-language-server_tmp_tmpkir0kenl_Test_vacid0_Composite_Adjust.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Valid (S : set<Composite>) : Bool :=
  sorry  -- TODO: implement complex function body

def Acyclic (S : set<Composite>) : Bool :=
  this in S ∧ (parent ≠ null → parent.Acyclic(S - {this}))


  (h_0 : U ≤ S ∧ Acyclic(U))
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks