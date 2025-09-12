/-
  Port of vericoding_dafnybench_0381_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

function list_find<K(==),V(!new)>(k:K,l:List<(K,V)>) : Option<V>
  sorry  -- TODO: implement function body

function list_remove<K(==,!new),V(!new)>(k:K, l:List<(K,V)>) : List<(K,V)>
  sorry  -- TODO: implement complex function body

def hash (key : K) : Int :=
  sorry  -- TODO: implement function body

def bucket (k : K) (n : Int) : Int :=
  hash(k) % n


  (h_0 : RepInv())
  : RepInv() ∧ elems == map[] ∧ fresh(Repr - old(Repr))
  := by
  sorry  -- TODO: implement proof


  (h_0 : RepInv())
  : RepInv() ∧ fresh(Repr - old(Repr)) ∧ ∀ key :: key in old(elems) → key in elems ∧ ∀ k v, k in old(elems) ∧ old(elems)[k] == Some(v) → k in elems ∧ elems[k]! == Some(v)
  := by
  sorry  -- TODO: implement proof


  (h_0 : newData ≠ data)
  (h_1 : 0 < oldSize == data.size)
  (h_2 : newData.size == 2 * oldSize == newSize)
  (h_3 : ∀ k v, mem((k,v), l) → bucket(k, oldSize) == i)
  (h_4 : ∀ j :: 0 ≤ j < newSize → valid_hash(newData, j))
  (h_5 : ∀ k v, ()
  := by
  sorry  -- TODO: implement proof

def find (k : K) : Option<V> :=
  sorry  -- TODO: implement function body

theorem find_spec (k : K) (r : Option<V>) :=
  (h_0 : RepInv())
  : RepInv() ∧ match r
  := by
  sorry  -- TODO: implement proof


  (h_0 : RepInv())
  : RepInv() ∧ fresh(Repr - old(Repr)) ∧ k !in elems ∨ elems[k]! == None ∧ ∀ key :: key ≠ k ∧ key in old(elems) → key in elems ∧ elems[key]! == old(elems[key]!)
  := by
  sorry  -- TODO: implement proof


  (h_0 : RepInv())
  : RepInv() ∧ fresh(Repr - old(Repr)) ∧ k in elems ∧ elems[k]! == Some(v) ∧ ∀ key :: key ≠ k ∧ key in old(elems) → key in elems
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks