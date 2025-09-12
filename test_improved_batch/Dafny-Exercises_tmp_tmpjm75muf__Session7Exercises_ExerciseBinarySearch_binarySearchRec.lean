/-
  Port of Dafny-Exercises_tmp_tmpjm75muf__Session7Exercises_ExerciseBinarySearch_binarySearchRec.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def binarySearchRec (v : Array Int) (elem : Int) (c : Int) (f : Int) : Int :=
  sorry  -- TODO: implement function body

theorem binarySearchRec_spec (v : Array Int) (elem : Int) (c : Int) (f : Int) (p : Int) :=
  (h_0 : sorted(v[0..v.size]))
  (h_1 : 0≤c≤f+1≤v.size//0≤c≤v.size ∧ -1≤f<v.size ∧ c≤f+1)
  (h_2 : ∀ k::0≤k<c → v[k]!≤elem)
  (h_3 : ∀ k::f<k<v.size → v[k]!>elem)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks