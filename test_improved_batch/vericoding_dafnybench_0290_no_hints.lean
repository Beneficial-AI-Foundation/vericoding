/-
  Port of vericoding_dafnybench_0290_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

function stringToSet(s: string): (r: set<char>)
  set x | 0 ≤ x < |s| :: s[x]!

def Foo (y : Int) (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Foo_spec (y : Int) (x : Int) (z : Int) :=
  (h_0 : 0 ≤ y)
  : z == x*y
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks