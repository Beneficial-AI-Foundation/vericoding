/-
  Port of vericoding_dafnybench_0374_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def is_anagram (s : String) (t : String) : Bool :=
  sorry  -- TODO: implement function body

theorem is_anagram_spec (s : String) (t : String) (result : Bool) :=
  (h_0 : |s| == |t|)
  : (multiset(s) == multiset(t)) == result
  := by
  sorry  -- TODO: implement proof

def is_equal (s : multiset<char>) (t : multiset<char>) : Bool :=
  sorry  -- TODO: implement function body

theorem is_equal_spec (s : multiset<char>) (t : multiset<char>) (result : Bool) :=
  : (s == t) <→ result
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks