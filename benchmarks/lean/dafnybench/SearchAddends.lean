/-
  Port of assertive-programming-assignment-1_tmp_tmp3h_cj44u_SearchAddends_spec.dfy
  
  This specification describes finding two elements in a sorted sequence that sum to a target value.
  The main function FindAddends takes:
  - A sorted sequence of integers
  - A target sum x
  
  Returns indices i and j such that q[i] + q[j] = x.
-/

namespace DafnyBenchmarks

/-- Predicate to check if a list is sorted -/
def Sorted : List Int → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x ≤ y ∧ Sorted (y :: xs)

/-- Predicate to check if there exist two elements that sum to x -/
def HasAddends (q : List Int) (x : Int) : Prop :=
  ∃ i j, i < j ∧ j < q.length ∧ q[i]! + q[j]! = x

/-- Find two indices whose elements sum to x -/
def findAddends (q : List Int) (x : Int) : Nat × Nat := sorry

/-- Specification for findAddends -/
theorem findAddends_spec (q : List Int) (x : Int) 
    (h1 : Sorted q) 
    (h2 : HasAddends q x) :
    let (i, j) := findAddends q x
    i < j ∧ j < q.length ∧ q[i]! + q[j]! = x := by
  sorry

/-- Helper predicate: checks if index is valid -/
def IsValidIndex {T : Type} (q : List T) (i : Nat) : Prop := i < q.length

/-- Helper predicate: checks if indices are ordered -/
def AreOrderedIndices {T : Type} (q : List T) (i j : Nat) : Prop := i < j ∧ j < q.length

/-- Helper predicate: checks if indices give addends -/
def AreAddendsIndices (q : List Int) (x : Int) (i j : Nat) : Prop :=
  AreOrderedIndices q i j ∧ q[i]! + q[j]! = x

/-- Helper predicate: checks if addends exist in range -/
def HasAddendsInIndicesRange (q : List Int) (x : Int) (i j : Nat) : Prop :=
  ∃ p q', i ≤ p ∧ p < q' ∧ q' ≤ j ∧ q' < q.length ∧ q[p]! + q[q']! = x

/-- Loop invariant for the search algorithm -/
def LoopInv (q : List Int) (x : Int) (i j : Nat) (sum : Int) : Prop :=
  Sorted q ∧ i ≤ j ∧ j ≤ q.length ∧
  (sum < x → ∀ k, i ≤ k → k < j → q[k]! ≤ q[j - 1]!) ∧
  (sum > x → ∀ k, i < k → k ≤ j → q[i]! ≤ q[k]!)

end DafnyBenchmarks
