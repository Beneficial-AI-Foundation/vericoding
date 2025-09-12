/-
  Port of Software-building-and-verification-Projects_tmp_tmp5tm1srrn_CVS-projeto_handout2_find.dfy
  
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

def find (k : K) : Option<V> :=
  sorry  -- TODO: implement function body

theorem find_spec (k : K) (r : Option<V>) :=
  (h_0 : RepInv())
  : RepInv() ∧ match r
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks