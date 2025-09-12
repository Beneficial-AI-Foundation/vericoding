/-
  Port of vericoding_dafnybench_0122_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

function A(m: map<int, nat>): (s:multiset<int>)
  sorry  -- TODO: implement function body

def Add (elem : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem Add_spec (elem : Int) (didChange : Bool) :=
  := by
  sorry  -- TODO: implement proof

def Remove (elem : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem Remove_spec (elem : Int) (didChange : Bool) :=
  := by
  sorry  -- TODO: implement proof

def Length  : Int :=
  sorry  -- TODO: implement function body

theorem Length_spec (len : Int) :=
  (h_0 : Valid())
  : Valid() ∧ len == |theMultiset|
  := by
  sorry  -- TODO: implement proof

def equals (other : MyMultiset) : Bool :=
  sorry  -- TODO: implement function body

theorem equals_spec (other : MyMultiset) (equal? : Bool) :=
  (h_0 : Valid())
  (h_1 : other.Valid())
  : Valid() ∧ equal? <→ theMultiset == other.theMultiset
  := by
  sorry  -- TODO: implement proof

def getElems  : seq<int> :=
  sorry  -- TODO: implement function body

theorem getElems_spec (elems : seq<int>) :=
  (h_0 : Valid())
  : Valid() ∧ multiset(elems) == theMultiset
  := by
  sorry  -- TODO: implement proof

def Add (elem : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem Add_spec (elem : Int) (didChange : Bool) :=
  := by
  sorry  -- TODO: implement proof

def Remove (elem : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem Remove_spec (elem : Int) (didChange : Bool) :=
  := by
  sorry  -- TODO: implement proof

def Length  : Int :=
  sorry  -- TODO: implement function body

theorem Length_spec (len : Int) :=
  (h_0 : Valid())
  : len == |theMultiset|
  := by
  sorry  -- TODO: implement proof

def equals (other : MyMultiset) : Bool :=
  sorry  -- TODO: implement function body

theorem equals_spec (other : MyMultiset) (equal? : Bool) :=
  (h_0 : Valid())
  (h_1 : other.Valid())
  : Valid() ∧ equal? <→ theMultiset == other.theMultiset
  := by
  sorry  -- TODO: implement proof

def getElems  : seq<int> :=
  sorry  -- TODO: implement function body

theorem getElems_spec (elems : seq<int>) :=
  (h_0 : Valid())
  : Valid() ∧ multiset(elems) == theMultiset
  := by
  sorry  -- TODO: implement proof

def Map2Seq (m : map<int) nat> : seq<int> :=
  sorry  -- TODO: implement function body

theorem Map2Seq_spec (m : map<int) nat> (s : seq<int>) :=
  (h_0 : ∀ i | i in m.Keys :: i in m.Keys <→ m[i]! > 0)
  : ∀ i | i in m.Keys :: multiset(s)[i] == m[i]! ∧ ∀ i | i in m.Keys :: i in s ∧ A(m) == multiset(s) ∧ (∀ i | i in m :: m[i]! == multiset(s)[i]) ∧ (m == map[] <→ multiset(s) == multiset{})
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks