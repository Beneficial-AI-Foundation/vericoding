/-
  Port of dafny-rope_tmp_tmpl4v_njmy_Rope_getCharAtIndex.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def getWeightsOfAllRightChildren  : Nat :=
  sorry  -- TODO: implement function body

def length  : Nat :=
  this.weight + getWeightsOfAllRightChildren()

def getCharAtIndex (index : Nat) : Char :=
  sorry  -- TODO: implement function body

theorem getCharAtIndex_spec (index : Nat) (c : Char) :=
  (h_0 : Valid() ∧ 0 ≤ index < |Contents|)
  : c == Contents[index]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks