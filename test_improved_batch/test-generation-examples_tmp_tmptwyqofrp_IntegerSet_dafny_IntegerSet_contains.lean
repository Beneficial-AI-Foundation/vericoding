/-
  Port of test-generation-examples_tmp_tmptwyqofrp_IntegerSet_dafny_IntegerSet_contains.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def intersect_length (s1 : seq<int>) (s2 : seq<int>) (count : Int) (start : Int) (stop : Int) : Int :=
  sorry  -- TODO: implement function body

def union_length (s1 : seq<int>) (s2 : seq<int>) (count : Int) (i : Int) (stop : Int) : Int :=
  sorry  -- TODO: implement function body

def contains (element : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem contains_spec (element : Int) (contains : Bool) :=
  : contains == (element in elements) ∧ elements == old(elements)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks