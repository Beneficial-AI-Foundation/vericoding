/-
  Port of vericoding_dafnybench_0137_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def push1 (element : T) : Bool :=
  sorry  -- TODO: implement function body

theorem push1_spec (element : T) (FullStatus : Bool) :=
  (h_0 : Valid())
  := by
  sorry  -- TODO: implement proof

def push2 (element : T) : Bool :=
  sorry  -- TODO: implement function body

theorem push2_spec (element : T) (FullStatus : Bool) :=
  (h_0 : Valid())
  := by
  sorry  -- TODO: implement proof

def pop1  : Bool :=
  sorry  -- TODO: implement function body

theorem pop1_spec (EmptyStatus : Bool) :=
  (h_0 : Valid())
  := by
  sorry  -- TODO: implement proof

def pop2  : Bool :=
  sorry  -- TODO: implement function body

theorem pop2_spec (EmptyStatus : Bool) :=
  (h_0 : Valid())
  := by
  sorry  -- TODO: implement proof

def peek1  : Bool :=
  sorry  -- TODO: implement function body

theorem peek1_spec (EmptyStatus : Bool) :=
  (h_0 : Valid())
  : Empty1() → EmptyStatus == false ∧ !Empty1() → EmptyStatus == true ∧ TopItem == s1[|s1|-1] ∧ Valid()
  := by
  sorry  -- TODO: implement proof

def peek2  : Bool :=
  sorry  -- TODO: implement function body

theorem peek2_spec (EmptyStatus : Bool) :=
  (h_0 : Valid())
  : Empty2() → EmptyStatus == false ∧ !Empty2() → EmptyStatus == true ∧ TopItem == s2[|s2|-1] ∧ Valid()
  := by
  sorry  -- TODO: implement proof

def search1 (Element : T) : Int :=
  sorry  -- TODO: implement function body

theorem search1_spec (Element : T) (position : Int) :=
  (h_0 : Valid())
  : position == -1 ∨ position ≥ 1 ∧ position ≥ 1 → ∃ i, 0 ≤i < |s1| ∧ s1[i]! == Element ∧ !Empty1() ∧ position == -1 → ∀ i :: 0 ≤ i < |s1| → s1[i]! ≠ Element ∨ Empty1() ∧ Valid()
  := by
  sorry  -- TODO: implement proof

def search3 (Element : T) : Int :=
  sorry  -- TODO: implement function body

theorem search3_spec (Element : T) (position : Int) :=
  (h_0 : Valid())
  : position == -1 ∨ position ≥ 1 ∧ position ≥ 1 → ∃ i, 0 ≤i < |s2| ∧ s2[i]! == Element ∧ !Empty2()
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks