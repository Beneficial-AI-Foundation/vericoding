/-
  Port of vericoding_dafnybench_0189_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def even (n : Int) : Bool :=
  sorry  -- TODO: implement complex function body

def is_even (n : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem is_even_spec (n : Int) (r : Bool) :=
  (h_0 : n ≥ 0;)
  : r <→ even(n);
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks