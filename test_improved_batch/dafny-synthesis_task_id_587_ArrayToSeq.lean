/-
  Port of dafny-synthesis_task_id_587_ArrayToSeq.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def ArrayToSeq (a : Array Int) : seq<int> :=
  sorry  -- TODO: implement function body

theorem ArrayToSeq_spec (a : Array Int) (s : seq<int>) :=
  (h_0 : a ≠ null)
  : |s| == a.size ∧ ∀ i :: 0 ≤ i < a.size → s[i]! == a[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks