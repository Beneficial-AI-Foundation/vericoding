/-
  Port of Software-building-and-verification-Projects_tmp_tmp5tm1srrn_CVS-projeto_handout2_clear.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

function list_find<K(==),V(!new)>(k:K,l:List<(K,V)>) : Option<V>
  sorry  -- TODO: implement function body

function list_remove<K(==,!new),V(!new)>(k:K, l:List<(K,V)>) : List<(K,V)>
  sorry  -- TODO: implement function body

def hash (key : K) : Int :=
  sorry  -- TODO: implement function body

def bucket (k : K) (n : Int) : Int :=
  hash(k) % n


  (h_0 : RepInv())
  : RepInv() ∧ elems == map[] ∧ fresh(Repr - old(Repr))
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks