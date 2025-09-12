/-
  Port of vericoding_dafnybench_0208_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

def popFront  : Odd :=
  sorry  -- TODO: implement function body

theorem popFront_spec (x : Odd) :=
  := by
  sorry  -- TODO: implement proof

def popBack  : Odd :=
  sorry  -- TODO: implement function body

theorem popBack_spec (x : Odd) :=
  := by
  sorry  -- TODO: implement proof

def length  : Nat :=
  sorry  -- TODO: implement function body

theorem length_spec (n : Nat) :=
  : n == |s|
  := by
  sorry  -- TODO: implement proof

def at (index : Nat) : Odd :=
  sorry  -- TODO: implement function body

theorem at_spec (index : Nat) (x : Odd) :=
  (h_0 : 0 ≤ index < |s|)
  := by
  sorry  -- TODO: implement proof

def BinarySearch (element : Odd) : Int :=
  sorry  -- TODO: implement function body

theorem BinarySearch_spec (element : Odd) (index : Int) :=
  (h_0 : ∀ i, j :: 0 ≤ i < j < |s| → s[i]! ≤ s[j]!)
  : 0 ≤ index → index < |s| ∧ s[index]! == element ∧ index == -1 → element !in s[..]
  := by
  sorry  -- TODO: implement proof

def mergedWith (l2 : OddList) : OddList :=
  sorry  -- TODO: implement function body

theorem mergedWith_spec (l2 : OddList) (l : OddList) :=
  (h_0 : Valid())
  (h_1 : l2.Valid())
  (h_2 : this.capacity ≥ 0)
  (h_3 : l2.capacity ≥ 0)
  (h_4 : ∀ i, j :: 0 ≤ i < j < |s| → s[i]! ≤ s[j]!)
  (h_5 : ∀ i, j :: 0 ≤ i < j < |l2.s| → l2.s[i]! ≤ l2.s[j]!)
  : l.capacity == this.capacity + l2.capacity ∧ |l.s| == |s| + |l2.s|
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

def popFront  : Odd :=
  sorry  -- TODO: implement function body

theorem popFront_spec (x : Odd) :=
  := by
  sorry  -- TODO: implement proof

def popBack  : Odd :=
  sorry  -- TODO: implement function body

theorem popBack_spec (x : Odd) :=
  := by
  sorry  -- TODO: implement proof

def length  : Nat :=
  sorry  -- TODO: implement function body

theorem length_spec (n : Nat) :=
  : n == |s|
  := by
  sorry  -- TODO: implement proof

def at (index : Nat) : Odd :=
  sorry  -- TODO: implement function body

theorem at_spec (index : Nat) (x : Odd) :=
  (h_0 : 0 ≤ index < |s|)
  : s[index]! == x
  := by
  sorry  -- TODO: implement proof

def BinarySearch (element : Odd) : Int :=
  sorry  -- TODO: implement function body

theorem BinarySearch_spec (element : Odd) (index : Int) :=
  (h_0 : ∀ i, j :: 0 ≤ i < j < |s| → s[i]! ≤ s[j]!)
  : 0 ≤ index → index < |s| ∧ s[index]! == element ∧ index == -1 → element !in s[..]
  := by
  sorry  -- TODO: implement proof

def mergedWith (l2 : OddList) : OddList :=
  sorry  -- TODO: implement function body

theorem mergedWith_spec (l2 : OddList) (l : OddList) :=
  (h_0 : Valid())
  (h_1 : l2.Valid())
  (h_2 : this.capacity ≥ 0)
  (h_3 : l2.capacity ≥ 0)
  (h_4 : ∀ i, j :: 0 ≤ i < j < |s| → s[i]! ≤ s[j]!)
  (h_5 : ∀ i, j :: 0 ≤ i < j < |l2.s| → l2.s[i]! ≤ l2.s[j]!)
  : l.capacity == this.capacity + l2.capacity ∧ |l.s| == |s| + |l2.s|
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

def length  : Nat :=
  sorry  -- TODO: implement function body

theorem length_spec (n : Nat) :=
  : n == |l|
  := by
  sorry  -- TODO: implement proof

def at (index : Int) : T :=
  sorry  -- TODO: implement function body

theorem at_spec (index : Int) (x : T) :=
  (h_0 : |l| > 0)
  : l[index % |l|] == x
  := by
  sorry  -- TODO: implement proof

def nextAfter (index : Int) : T :=
  sorry  -- TODO: implement function body

theorem nextAfter_spec (index : Int) (x : T) :=
  (h_0 : |l| > 0)
  : |l| == 1 → x == l[0]! ∧ |l| > 1 ∧ index % |l| == (|l| - 1) → x == l[0]! ∧ |l| > 1 ∧ 0 ≤ index ∧ |l| < (|l| - 1) → x == l[index % |l| + 1]
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

def length  : Nat :=
  sorry  -- TODO: implement function body

theorem length_spec (n : Nat) :=
  : n == |l|
  := by
  sorry  -- TODO: implement proof

def at (index : Int) : T :=
  sorry  -- TODO: implement function body

theorem at_spec (index : Int) (x : T) :=
  (h_0 : |l| > 0)
  : l[index % |l|] == x
  := by
  sorry  -- TODO: implement proof

def nextAfter (index : Int) : T :=
  sorry  -- TODO: implement function body

theorem nextAfter_spec (index : Int) (x : T) :=
  (h_0 : |l| > 0)
  : |l| == 1 → x == l[0]! ∧ |l| > 1 ∧ index % |l| == (|l| - 1) → x == l[0]! ∧ |l| > 1 ∧ 0 ≤ index ∧ |l| < (|l| - 1) → x == l[index % |l| + 1]
  := by
  sorry  -- TODO: implement proof

def isIn (element : T) : Bool :=
  sorry  -- TODO: implement function body

theorem isIn_spec (element : T) (b : Bool) :=
  : |l| == 0 → b == false ∧ |l| > 0 ∧ b == true → ∃ i, 0 ≤ i < |l| ∧ l[i]! == element ∧ |l| > 0 ∧ b == false → !∃ i, 0 ≤ i < |l| ∧ l[i]! == element
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks