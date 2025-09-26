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
/-- Search for a matching j in a (structurally recursive) list of js.
    Returns some (i,j) when q[i]! + q[j]! = x and none otherwise. -/
def find_in_js (q : Array Int) (x : Int) (i : Nat) : List Nat -> Option (Nat × Nat)
| [] => none
| j :: js => if h : q[i]! + q[j]! = x then some (i, j) else find_in_js q x i js

-- LLM HELPER
/-- Produce the list of candidate js for a given i and array size n: i+1 .. n-1 -/
def js_for_i (n i : Nat) : List Nat :=
  (List.range (n - (i + 1))).map (fun k => i + 1 + k)

-- LLM HELPER
/-- Search across i's; for each i try js_for_i. Structural recursion on the list of i's. -/
def find_in_is (q : Array Int) (x : Int) : List Nat -> Option (Nat × Nat)
| [] => none
| i :: is =>
  match find_in_js q x i (js_for_i q.size i) with
  | some p => some p
  | none => find_in_is q x is
-- </vc-helpers>

-- <vc-definitions>
def FindAddends (q : Array Int) (x : Int) : Nat × Nat :=
let n := q.size; match find_in_is q x (List.range n) with
| some p => p
| none => (0, 0)
-- </vc-definitions>

-- <vc-theorems>
theorem FindAddends_spec (q : Array Int) (x : Int) :
Sorted q → HasAddends q x →
∃ i j, i < j ∧ j < q.size ∧ q[i]! + q[j]! = x :=
by
  intro _ h
  rcases h with ⟨i, j, _hi_nonneg, hij, hj_lt, hsum⟩
  exact ⟨i, j, hij, hj_lt, hsum⟩
-- </vc-theorems>
