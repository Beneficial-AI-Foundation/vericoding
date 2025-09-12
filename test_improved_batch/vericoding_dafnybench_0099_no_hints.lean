/-
  Port of vericoding_dafnybench_0099_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def CountEven (s : seq<int>) : Int :=
  sorry  -- TODO: implement complex function body

def mcountEven (v : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem mcountEven_spec (v : Array Int) (n : Int) :=
  (h_0 : positive(v[..]))
  :  n==CountEven(v[..])
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks