/-
  Port of dafny_projects_tmp_tmpjutqwjv4_tutorial_tutorial_BinarySearch.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def fib (n : Nat) : Nat :=
  sorry  -- TODO: implement complex function body

def update (s : seq<int>) (i : Int) (v : Int) : seq :=
  s[..i] + [v] + s[i+1..]

def count (a : seq<bool>) : Nat :=
  sorry  -- TODO: implement complex function body

def BinarySearch (a : Array Int) (value : Int) : Int :=
  sorry  -- TODO: implement function body

theorem BinarySearch_spec (a : Array Int) (value : Int) (index : Int) :=
  (h_0 : 0 ≤ a.size ∧ sorted(a))
  : 0 ≤ index → index < a.size ∧ a[index]! == value ∧ index < 0 → ∀ k :: 0 ≤ k < a.size → a[k]! ≠ value
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks