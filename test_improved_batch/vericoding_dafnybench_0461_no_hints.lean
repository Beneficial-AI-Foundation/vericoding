/-
  Port of vericoding_dafnybench_0461_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Up (n : Int) : Stream :=
  SCons(n, Up(n+1))

def FivesUp (n : Int) : Stream :=
  sorry  -- TODO: implement complex function body

def SAppend (xs : Stream) (ys : Stream) : Stream :=
  match xs case SNil => ys case SCons(x, rest) => SCons(x, SAppend(rest, ys))

end DafnyBenchmarks