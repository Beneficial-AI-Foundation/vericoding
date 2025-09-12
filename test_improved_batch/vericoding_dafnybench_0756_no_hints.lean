/-
  Port of vericoding_dafnybench_0756_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def AtLeastTwiceAsBigFunction (a : Int) (b : Int) : Bool :=
  a ≥ 2*b

def Double (a : Int) : Int :=
  2 * a

end DafnyBenchmarks