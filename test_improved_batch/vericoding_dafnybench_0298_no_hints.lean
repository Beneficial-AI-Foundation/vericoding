/-
  Port of vericoding_dafnybench_0298_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def toMultiset (s : String) : multiset<char> :=
  sorry  -- TODO: implement function body

theorem toMultiset_spec (s : String) (mset : multiset<char>) :=
  : multiset(s) == mset
  := by
  sorry  -- TODO: implement proof

def msetEqual (s : multiset<char>) (t : multiset<char>) : Bool :=
  sorry  -- TODO: implement function body

theorem msetEqual_spec (s : multiset<char>) (t : multiset<char>) (equal : Bool) :=
  : s == t <→ equal
  := by
  sorry  -- TODO: implement proof

def isAnagram (s : String) (t : String) : Bool :=
  sorry  -- TODO: implement function body

theorem isAnagram_spec (s : String) (t : String) (equal : Bool) :=
  : (multiset(s) == multiset(t)) == equal
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks