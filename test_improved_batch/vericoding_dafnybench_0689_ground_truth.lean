/-
  Port of vericoding_dafnybench_0689_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SqrSumRec (n : Int) : Int :=
  sorry  -- TODO: implement complex function body

def SqrSumBy6 (n : Int) : Int :=
  n * (n + 1) * (2 * n + 1)

def SqrSum (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem SqrSum_spec (n : Int) (s : Int) :=
  := by
  sorry  -- TODO: implement proof

def DivMod (a : Int) (b : Int) : Int :=
  sorry  -- TODO: implement function body

theorem DivMod_spec (a : Int) (b : Int) (q : Int) :=
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

def HoareTripleReqEns (i : Int) (k : Int) : Int :=
  sorry  -- TODO: implement function body

theorem HoareTripleReqEns_spec (i : Int) (k : Int) (k' : Int) :=
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

def SqrSum1 (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem SqrSum1_spec (n : Int) (s : Int) :=
  (h_0 : n ≥ 0)
  : s == SqrSumRec(n)  // s = 0^2 + 1^2 + 2^2 + ... + n^2 == n(n+1)(2n+1)/6
  := by
  sorry  -- TODO: implement proof

def SqrSum1 (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem SqrSum1_spec (n : Int) (s : Int) :=
  (h_0 : n ≥ 0)
  : s == SqrSumRec(n)
  := by
  sorry  -- TODO: implement proof

def DivMod1 (a : Int) (b : Int) : Int :=
  sorry  -- TODO: implement function body

theorem DivMod1_spec (a : Int) (b : Int) (q : Int) :=
  (h_0 : b > 0 ∧ a ≥ 0)
  : a == b*q + r ∧ 0 ≤ r < b
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks