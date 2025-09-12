/-
  Port of dafny_projects_tmp_tmpjutqwjv4_tutorial_tutorial_Find.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def fib (n : Nat) : Nat :=
  sorry  -- TODO: implement complex function body

def update (s : seq<int>) (i : Int) (v : Int) : seq :=
  s[..i] + [v] + s[i+1..]

def count (a : seq<bool>) : Nat :=
  sorry  -- TODO: implement complex function body

def Find (a : Array Int) (key : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Find_spec (a : Array Int) (key : Int) (index : Int) :=
  : 0 ≤ index → index < a.size ∧ a[index]! == key ∧ index < 0 → (∀ k :: 0 ≤ k < a.size → a[k]! ≠ key)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks