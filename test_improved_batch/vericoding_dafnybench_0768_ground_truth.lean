/-
  Port of vericoding_dafnybench_0768_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def intersect_length (s1 : seq<int>) (s2 : seq<int>) (count : Int) (start : Int) (stop : Int) : Int :=
  sorry  -- TODO: implement function body

def union_length (s1 : seq<int>) (s2 : seq<int>) (count : Int) (i : Int) (stop : Int) : Int :=
  sorry  -- TODO: implement function body

def size  : Int :=
  sorry  -- TODO: implement function body

theorem size_spec (size : Int) :=
  : size == |elements|
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

def contains (element : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem contains_spec (element : Int) (contains : Bool) :=
  : contains == (element in elements) ∧ elements == old(elements)
  := by
  sorry  -- TODO: implement proof

def intersect (s : Set) : Set :=
  sorry  -- TODO: implement function body

theorem intersect_spec (s : Set) (intersection : Set) :=
  (h_0 : ∀ i, j | 0 ≤ i < |s.elements| ∧ 0 ≤ j < |s.elements| ∧ i ≠ j :: s.elements[i]! ≠ s.elements[j]!)
  (h_1 : ∀ i, j | 0 ≤ i < |this.elements| ∧ 0 ≤ j < |this.elements| ∧ i ≠ j :: this.elements[i]! ≠ this.elements[j]!)
  : ∀ i : Int, i in intersection.elements <→ i in s.elements ∧ i in this.elements ∧ ∀ i : Int, i !in intersection.elements  <→ i !in s.elements ∨ i !in this.elements ∧ ∀ j, k | 0 ≤ j < |intersection.elements| ∧ 0 ≤ k < |intersection.elements| ∧ j ≠ k :: intersection.elements[j]! ≠ intersection.elements[k]! ∧ fresh(intersection)
  := by
  sorry  -- TODO: implement proof

def union (s : Set) : Set :=
  sorry  -- TODO: implement function body

theorem union_spec (s : Set) (union : Set) :=
  (h_0 : ∀ i, j | 0 ≤ i < |s.elements| ∧ 0 ≤ j < |s.elements| ∧ i ≠ j :: s.elements[i]! ≠ s.elements[j]!)
  (h_1 : ∀ i, j | 0 ≤ i < |this.elements| ∧ 0 ≤ j < |this.elements| ∧ i ≠ j :: this.elements[i]! ≠ this.elements[j]!)
  : ∀ i : Int, i in s.elements ∨ i in this.elements <→ i in union.elements ∧ ∀ i : Int, i !in s.elements ∧ i !in this.elements <→ i !in union.elements ∧ ∀ j, k | 0 ≤ j < |union.elements| ∧ 0 ≤ k < |union.elements| ∧ j ≠ k :: union.elements[j]! ≠ union.elements[k]! ∧ fresh(union)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks