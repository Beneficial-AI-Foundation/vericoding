/-
  Port of vericoding_dafnybench_0677_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def fib (n : Nat) : Nat :=
  sorry  -- TODO: implement complex function body

def update (s : seq<int>) (i : Int) (v : Int) : seq :=
  s[..i] + [v] + s[i+1..]

def count (a : seq<bool>) : Nat :=
  sorry  -- TODO: implement complex function body

def ComputeFib (n : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem ComputeFib_spec (n : Nat) (ret : Nat) :=
  : ret == fib(n)
  := by
  sorry  -- TODO: implement proof

def Find (a : Array Int) (key : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Find_spec (a : Array Int) (key : Int) (index : Int) :=
  : 0 ≤ index → index < a.size ∧ a[index]! == key ∧ index < 0 → (∀ k :: 0 ≤ k < a.size → a[k]! ≠ key)
  := by
  sorry  -- TODO: implement proof

def BinarySearch (a : Array Int) (value : Int) : Int :=
  sorry  -- TODO: implement function body

theorem BinarySearch_spec (a : Array Int) (value : Int) (index : Int) :=
  (h_0 : 0 ≤ a.size ∧ sorted(a))
  : 0 ≤ index → index < a.size ∧ a[index]! == value ∧ index < 0 → ∀ k :: 0 ≤ k < a.size → a[k]! ≠ value
  := by
  sorry  -- TODO: implement proof

def FindZero (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem FindZero_spec (a : Array Int) (index : Int) :=
  (h_0 : ∀ i :: 0 ≤ i < a.size → 0 ≤ a[i]!)
  (h_1 : ∀ i :: 0 < i < a.size → a[i-1]-1 ≤ a[i]!)
  : index < 0  → ∀ i :: 0 ≤ i < a.size → a[i]! ≠ 0 ∧ 0 ≤ index → index < a.size ∧ a[index]! == 0
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks