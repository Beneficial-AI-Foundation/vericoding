/-
  Port of vericoding_dafnybench_0063_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def remove_front (a : Array Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem remove_front_spec (a : Array Int) (c : Array Int) :=
  (h_0 : a.size>0)
  :  a[1..] == c[..]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks