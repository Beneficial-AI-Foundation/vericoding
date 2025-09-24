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
-- </vc-helpers>

-- <vc-definitions>
def FindAddends (q : Array Int) (x : Int) : Nat × Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FindAddends_spec (q : Array Int) (x : Int) :
Sorted q → HasAddends q x →
∃ i j, i < j ∧ j < q.size ∧ q[i]! + q[j]! = x :=
sorry
-- </vc-theorems>