/-
  Port of dafny-synthesis_task_id_784_ProductEvenOdd.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def FirstEvenOddIndices (lst : seq<int>) : Int :=
  sorry  -- TODO: implement function body

theorem FirstEvenOddIndices_spec (lst : seq<int>) (evenIndex : Int) :=
  (h_0 : |lst| ≥ 2)
  (h_1 : ∃ i, 0 ≤ i < |lst| ∧ IsEven(lst[i]!))
  (h_2 : ∃ i, 0 ≤ i < |lst| ∧ IsOdd(lst[i]!))
  : 0 ≤ evenIndex < |lst| ∧ 0 ≤ oddIndex < |lst|
  := by
  sorry  -- TODO: implement proof

def ProductEvenOdd (lst : seq<int>) : Int :=
  sorry  -- TODO: implement function body

theorem ProductEvenOdd_spec (lst : seq<int>) (product : Int) :=
  (h_0 : |lst| ≥ 2)
  (h_1 : ∃ i, 0 ≤ i < |lst| ∧ IsEven(lst[i]!))
  (h_2 : ∃ i, 0 ≤ i < |lst| ∧ IsOdd(lst[i]!))
  : ∃ i, j :: 0 ≤ i < |lst| ∧ IsEven(lst[i]!) ∧ IsFirstEven(i, lst) ∧
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks