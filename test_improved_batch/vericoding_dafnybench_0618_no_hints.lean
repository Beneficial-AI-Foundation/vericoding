/-
  Port of vericoding_dafnybench_0618_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsBreakEven (costPrice : Int) (sellingPrice : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem IsBreakEven_spec (costPrice : Int) (sellingPrice : Int) (result : Bool) :=
  (h_0 : costPrice ≥ 0 ∧ sellingPrice ≥ 0)
  : result <→ costPrice == sellingPrice
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks