/-
  Port of vericoding_dafnybench_0486_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Valid (S : set<Composite>) : Bool :=
  sorry  -- TODO: implement complex function body

def Acyclic (S : set<Composite>) : Bool :=
  this in S ∧ (parent ≠ null → parent.Acyclic(S - {this}))


  := by
  sorry  -- TODO: implement proof


  (h_0 : this in S ∧ Acyclic(S))
  (h_1 : ∀ c :: c in S → c.Valid(S))
  := by
  sorry  -- TODO: implement proof


  (h_0 : this in S ∧ Acyclic(S))
  (h_1 : ∀ c :: c in S → c.Valid(S))
  (h_2 : child in U)
  (h_3 : ∀ c :: c in U → c.Valid(U))
  (h_4 : S !! U)
  (h_5 : left == null ∨ right == null)
  (h_6 : child.parent == null)
  := by
  sorry  -- TODO: implement proof


  (h_0 : this in S ∧ Acyclic(S))
  (h_1 : ∀ c :: c in S → c.Valid(S))
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks