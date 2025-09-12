/-
  Port of vericoding_dafnybench_0007_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SetLessThan (numbers : set<int>) (threshold : Int) : set :=
  set i | i in numbers ∧ i < threshold

def seqSet (nums : seq<int>) (index : Nat) : set :=
  sorry  -- TODO: implement function body

def count (a : seq<bool>) : Nat :=
  sorry  -- TODO: implement complex function body


  := by
  sorry  -- TODO: implement proof

def GetInsertIndex (a : Array Int) (limit : Int) (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem GetInsertIndex_spec (a : Array Int) (limit : Int) (x : Int) (idx : Int) :=
  := by
  sorry  -- TODO: implement proof

def InsertSorted (a : Array Int) (key : Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem InsertSorted_spec (a : Array Int) (key : Int) (b : Array Int) :=
  (h_0 : sorted_eq(a[..]))
  : sorted_eq(b[..])
  := by
  sorry  -- TODO: implement proof

def InsertIntoSorted (a : Array Int) (limit : Int) (key : Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem InsertIntoSorted_spec (a : Array Int) (limit : Int) (key : Int) (b : Array Int) :=
  (h_0 : key > 0)
  (h_1 : key !in a[..])
  (h_2 : 0 ≤ limit < a.size)
  (h_3 : ∀ i :: 0 ≤ i < limit → a[i]! > 0)
  (h_4 : ∀ i :: limit ≤ i < a.size → a[i]! == 0)
  (h_5 : sorted(a[..limit]))
  : b.size == a.size ∧ sorted(b[..(limit+ 1)]) ∧ ∀ i :: limit + 1 ≤ i < b.size → b[i]! == 0 ∧ ∀ i :: 0 ≤ i < limit → a[i]! in b[..] ∧ ∀ i :: 0 ≤ i < limit + 1 → b[i]! > 0
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks