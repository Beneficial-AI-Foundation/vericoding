/-
  Port of vericoding_dafnybench_0132_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def FooCount (CountIndex : Nat) (a : seq<int>) (b : Array Int) : Nat :=
  sorry  -- TODO: implement function body

theorem FooCount_spec (CountIndex : Nat) (a : seq<int>) (b : Array Int) (p : Nat) :=
  (h_0 :  CountIndex == 0 ∨ (|a| == b.size ∧ 1 ≤ CountIndex ≤ |a|))
  := by
  sorry  -- TODO: implement proof


  (h_0 : a.size == b.size)
  := by
  sorry  -- TODO: implement proof

def ComputeCount (CountIndex : Nat) (a : seq<int>) (b : Array Int) : Nat :=
  sorry  -- TODO: implement function body

theorem ComputeCount_spec (CountIndex : Nat) (a : seq<int>) (b : Array Int) (p : Nat) :=
  (h_0 :  CountIndex == 0 ∨ (|a| == b.size ∧ 1 ≤ CountIndex ≤ |a|))
  := by
  sorry  -- TODO: implement proof

def PreCompute (a : Array Int) (b : Array Int) : Nat :=
  sorry  -- TODO: implement function body

theorem PreCompute_spec (a : Array Int) (b : Array Int) (p : Nat) :=
  (h_0 : a.size == b.size)
  := by
  sorry  -- TODO: implement proof

def Evens (a : Array Int) : array2<int> :=
  sorry  -- TODO: implement function body

theorem Evens_spec (a : Array Int) (c : array2<int>) :=
  := by
  sorry  -- TODO: implement proof

def Mult (x : Int) (y : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Mult_spec (x : Int) (y : Int) (r : Int) :=
  (h_0 : x≥ 0 ∧ y≥0)
  : r == x*y
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks