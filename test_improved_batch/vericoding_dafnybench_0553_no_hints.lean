/-
  Port of vericoding_dafnybench_0553_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def AnyValueExists (seq1 : seq<int>) (seq2 : seq<int>) : Bool :=
  sorry  -- TODO: implement function body

theorem AnyValueExists_spec (seq1 : seq<int>) (seq2 : seq<int>) (result : Bool) :=
  : result <→ (∃ i, 0 ≤ i < |seq1| ∧ seq1[i]! in seq2)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks