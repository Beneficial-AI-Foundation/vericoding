/-
  Port of vericoding_dafnybench_0332_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def min (r1 : Float) (r2 : Float) : Float :=
  sorry  -- TODO: implement function body

def max (r1 : Float) (r2 : Float) : Float :=
  sorry  -- TODO: implement function body

def intersect (i1 : Interval) (i2 : Interval) : Interval :=
  sorry  -- TODO: implement function body

def union (i1 : Interval) (i2 : Interval) : Interval :=
  Interval(min(i1.lo, i2.lo), max(i1.hi, i2.hi))

end DafnyBenchmarks