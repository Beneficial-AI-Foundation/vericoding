/-
  Port of vericoding_dafnybench_0112_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def ArraySplit (a : Array Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem ArraySplit_spec (a : Array Int) (b : Array Int) :=
  : fresh(b) ∧ fresh(c) ∧ a[..] == b[..] + c[..] ∧ a.size == b.size + c.size ∧ a.size > 1 → a.size > b.size ∧ a.size > 1 → a.size > c.size
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks