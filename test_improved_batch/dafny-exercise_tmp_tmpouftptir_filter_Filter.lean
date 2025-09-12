/-
  Port of dafny-exercise_tmp_tmpouftptir_filter_Filter.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Filter (a : seq<char>) (b : set<char>) : set<char> :=
  sorry  -- TODO: implement function body

theorem Filter_spec (a : seq<char>) (b : set<char>) (c : set<char>) :=
  : ∀ x :: x in a ∧ x in b <→ x in c
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks