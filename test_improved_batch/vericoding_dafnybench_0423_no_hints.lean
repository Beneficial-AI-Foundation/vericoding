/-
  Port of vericoding_dafnybench_0423_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def splitHelper (s : String) (separator : String) (index : Nat) (sindex : Nat) (results : seq<string>) : seq :=
  sorry  -- TODO: implement function body

def split (s : String) (separator : String) : seq :=
  splitHelper(s, separator, 0, 0, [])

def splitOnBreak (s : String) : seq :=
  sorry  -- TODO: implement function body

def splitOnDoubleBreak (s : String) : seq :=
  sorry  -- TODO: implement function body

end DafnyBenchmarks