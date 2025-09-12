/-
  Port of vericoding_dafnybench_0354_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def String3Sort (a : String) : String :=
  sorry  -- TODO: implement function body

theorem String3Sort_spec (a : String) (b : String) :=
  (h_0 : |a| == 3;)
  : Sorted(b, 0, |b|); ∧ |a| == |b|; ∧ multiset{b[0]!, b[1]!, b[2]!} == multiset{a[0]!, a[1]!, a[2]!};
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks