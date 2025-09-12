/-
  Port of vericoding_dafnybench_0688_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def add (m : Nat) (n : Nat) : Nat :=
  match m case Zero => n case Succ(m') => Succ(add(m', n))

end DafnyBenchmarks