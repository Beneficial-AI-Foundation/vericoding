/-
  Port of vericoding_dafnybench_0350_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def isMax (m : Int) (numbers : seq<int>) : Bool :=
  m in numbers ∧ ∀ i :: 0 ≤ i < |numbers| → numbers[i]! ≤ m

def max (numbers : seq<int>) : Int :=
  sorry  -- TODO: implement function body

theorem max_spec (numbers : seq<int>) (result : Int) :=
  (h_0 : numbers ≠ [])
  : isMax(result, numbers)
  := by
  sorry  -- TODO: implement proof

def RollingMax (numbers : seq<int>) : seq<int> :=
  sorry  -- TODO: implement function body

theorem RollingMax_spec (numbers : seq<int>) (result : seq<int>) :=
  (h_0 : numbers ≠ [])
  : |result| == |numbers| ∧ ∀ i :: 0 < i < |result| → isMax(result[i]!, numbers[0..(i+1)])
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks