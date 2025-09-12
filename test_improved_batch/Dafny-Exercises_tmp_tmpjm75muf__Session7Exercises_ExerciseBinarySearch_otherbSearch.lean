/-
  Port of Dafny-Exercises_tmp_tmpjm75muf__Session7Exercises_ExerciseBinarySearch_otherbSearch.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def binarySearch (v : Array Int) (elem : Int) : Int :=
  sorry  -- TODO: implement function body

theorem binarySearch_spec (v : Array Int) (elem : Int) (p : Int) :=
  (h_0 : sorted(v[0..v.size]))
  : -1≤p<v.size ∧ (∀ u::0≤u≤p → v[u]!≤elem) ∧ (∀ w::p<w<v.size → v[w]!>elem)
  := by
  sorry  -- TODO: implement proof

def otherbSearch (v : Array Int) (elem : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem otherbSearch_spec (v : Array Int) (elem : Int) (b : Bool) :=
  (h_0 : sorted(v[0..v.size]))
  : 0≤p≤v.size ∧ b == (elem in v[0..v.size]) ∧ b → p<v.size ∧ v[p]≠=elem ∧ !b → (∀ u::0≤u<p → v[u]!<elem) ∧
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks