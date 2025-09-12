/-
  Port of vericoding_dafnybench_0230_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def factorial (n : Int) : Int :=
  sorry  -- TODO: implement complex function body

def sumSerie (n : Int) : Int :=
  sorry  -- TODO: implement complex function body

def multipleReturns (x : Int) (y : Int) : Int :=
  sorry  -- TODO: implement function body

theorem multipleReturns_spec (x : Int) (y : Int) (more : Int) :=
  (h_0 : y > 0)
  : less < x < more
  := by
  sorry  -- TODO: implement proof

def multipleReturns2 (x : Int) (y : Int) : Int :=
  sorry  -- TODO: implement function body

theorem multipleReturns2_spec (x : Int) (y : Int) (more : Int) :=
  (h_0 : y > 0)
  : more + less == 2*x
  := by
  sorry  -- TODO: implement proof

def multipleReturns3 (x : Int) (y : Int) : Int :=
  sorry  -- TODO: implement function body

theorem multipleReturns3_spec (x : Int) (y : Int) (more : Int) :=
  (h_0 : y > 0)
  : more - less == 2*y
  := by
  sorry  -- TODO: implement proof

def ComputeFact (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem ComputeFact_spec (n : Int) (f : Int) :=
  (h_0 : n ≥0)
  : f== factorial(n)
  := by
  sorry  -- TODO: implement proof

def ComputeFact2 (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem ComputeFact2_spec (n : Int) (f : Int) :=
  (h_0 : n ≥0)
  : f== factorial(n)
  := by
  sorry  -- TODO: implement proof

def Sqare (a : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Sqare_spec (a : Int) (x : Int) :=
  (h_0 : a≥1)
  : x == a*a
  := by
  sorry  -- TODO: implement proof

def Sqare2 (a : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Sqare2_spec (a : Int) (x : Int) :=
  (h_0 : a≥1)
  : x == a*a
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks