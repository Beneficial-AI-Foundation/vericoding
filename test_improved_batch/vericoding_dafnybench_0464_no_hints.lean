/-
  Port of vericoding_dafnybench_0464_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def M1 (f : map<int) bool> (i : Int) : Bool :=
  sorry  -- TODO: implement function body

def M2 (f : map<int) bool> (i : Int) : Bool :=
  M1(map j | j in f :: f[j]!, i)

end DafnyBenchmarks