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
def Sorted (q : List Int) : Prop :=
  ∀ i j, 0 ≤ i ∧ i ≤ j ∧ j < q.length → q[i]! ≤ q[j]!

/-- Predicate to check if there exist two elements that sum to x -/
def HasAddends (q : List Int) (x : Int) : Prop :=
  ∃ i j, 0 ≤ i ∧ i < j ∧ j < q.length ∧ q[i]! + q[j]! = x

/-- Find two indices whose elements sum to x -/
def findAddends (q : List Int) (x : Int) : Nat × Nat :=
  -- Two-pointer approach for sorted array
  let rec search (i j : Nat) : Nat × Nat :=
    if h : i < j ∧ j < q.length then
      let sum := q[i]! + q[j]!
      if sum = x then (i, j)
      else if sum < x then search (i + 1) j
      else 
        if j = 0 then (0, 0)
        else search i (j - 1)
    else (0, 0)  -- Should not reach here given precondition
  termination_by j - i
  search 0 (q.length - 1)

/-- Specification for findAddends -/
theorem findAddends_spec (q : List Int) (x : Int) 
    (h1 : Sorted q) 
    (h2 : HasAddends q x) :
    let (i, j) := findAddends q x
    i < j ∧ j < q.length ∧ q[i]! + q[j]! = x := by
  sorry

/-- Helper predicate: checks if index is valid -/
def IsValidIndex {T : Type} (q : List T) (i : Nat) : Prop :=
  0 ≤ i ∧ i < q.length

/-- Helper predicate: checks if indices are ordered -/
def AreOrderedIndices {T : Type} (q : List T) (i j : Nat) : Prop :=
  0 ≤ i ∧ i < j ∧ j < q.length

/-- Helper predicate: checks if indices give addends -/
def AreAddendsIndices (q : List Int) (x : Int) (i j : Nat) : Prop :=
  IsValidIndex q i ∧ IsValidIndex q j → q[i]! + q[j]! = x

/-- Helper predicate: checks if addends exist in range -/
def HasAddendsInIndicesRange (q : List Int) (x : Int) (i j : Nat) : Prop :=
  AreOrderedIndices q i j → HasAddends (q.drop i |>.take (j + 1 - i)) x

/-- Loop invariant for the search algorithm -/
def LoopInv (q : List Int) (x : Int) (i j : Nat) (sum : Int) : Prop :=
  AreOrderedIndices q i j ∧
  HasAddendsInIndicesRange q x i j ∧
  AreAddendsIndices q sum i j

end DafnyBenchmarks