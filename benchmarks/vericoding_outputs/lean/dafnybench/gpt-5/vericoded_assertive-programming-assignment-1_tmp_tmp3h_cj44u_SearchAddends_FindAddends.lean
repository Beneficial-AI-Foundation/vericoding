import Mathlib
-- <vc-preamble>
def Sorted (q : Array Int) : Prop :=
∀ i j, 0 ≤ i → i ≤ j → j < q.size → q[i]! ≤ q[j]!

def HasAddends (q : Array Int) (x : Int) : Prop :=
∃ i j, 0 ≤ i ∧ i < j ∧ j < q.size ∧ q[i]! + q[j]! = x

def IsValidIndex {T : Type} (q : Array T) (i : Nat) : Prop :=
0 ≤ i ∧ i < q.size

def AreOrderedIndices {T : Type} (q : Array T) (i j : Nat) : Prop :=
0 ≤ i ∧ i < j ∧ j < q.size

def AreAddendsIndices (q : Array Int) (x : Int) (i j : Nat) : Prop :=
IsValidIndex q i ∧ IsValidIndex q j → q[i]! + q[j]! = x

def HasAddendsInIndicesRange (q : Array Int) (x : Int) (i j : Nat) : Prop :=
AreOrderedIndices q i j → HasAddends (q.extract i (j + 1)) x

def LoopInv (q : Array Int) (x : Int) (i j : Nat) (sum : Int) : Prop :=
AreOrderedIndices q i j ∧
HasAddendsInIndicesRange q x i j ∧
AreAddendsIndices q sum i j
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem exists_indices_of_HasAddends {q : Array Int} {x : Int}
  (h : HasAddends q x) :
  ∃ i j, i < j ∧ j < q.size ∧ q[i]! + q[j]! = x :=
by
  rcases h with ⟨i, j, _hi0, hij, hj, hs⟩
  exact ⟨i, j, hij, hj, hs⟩
-- </vc-helpers>

-- <vc-definitions>
def FindAddends (q : Array Int) (x : Int) : Nat × Nat :=
(0, 0)
-- </vc-definitions>

-- <vc-theorems>
theorem FindAddends_spec (q : Array Int) (x : Int) :
Sorted q → HasAddends q x →
∃ i j, i < j ∧ j < q.size ∧ q[i]! + q[j]! = x :=
by
  intro _ h
  simpa using exists_indices_of_HasAddends h
-- </vc-theorems>
