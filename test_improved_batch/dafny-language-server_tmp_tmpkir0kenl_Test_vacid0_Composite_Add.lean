/-
  Port of dafny-language-server_tmp_tmpkir0kenl_Test_vacid0_Composite_Add.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Valid (S : set<Composite>) : Bool :=
  sorry  -- TODO: implement complex function body

def Acyclic (S : set<Composite>) : Bool :=
  this in S ∧ (parent ≠ null → parent.Acyclic(S - {this}))


  (h_0 : this in S ∧ Acyclic(S))
  (h_1 : ∀ c :: c in S → c.Valid(S))
  (h_2 : child in U)
  (h_3 : ∀ c :: c in U → c.Valid(U))
  (h_4 : S !! U)
  (h_5 : left == null ∨ right == null)
  (h_6 : child.parent == null)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks