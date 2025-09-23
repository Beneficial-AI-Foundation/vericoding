-- <vc-preamble>
def SplitPoint (a : Array Int) (n : Nat) : Prop :=
∀ i j, 0 ≤ i ∧ i < n ∧ n ≤ j ∧ j < a.size → a[i]! ≤ a[j]!

def SwapFrame (a a' : Array Int) (lo hi : Nat) : Prop :=
(∀ i, (0 ≤ i ∧ i < lo) ∨ (hi ≤ i ∧ i < a.size) → a[i]! = a'[i]!)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Partition (a : Array Int) (lo hi : Int) : Int :=
sorry

def QuickSortAux (a : Array Int) (lo hi : Nat) : Array Int :=
sorry

def QuickSort (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem quicksort_spec (a : Array Int) :
let a' := QuickSort a
∀ i j, 0 ≤ i ∧ i < j ∧ j < a'.size → a'[i]! ≤ a'[j]! :=
sorry
-- </vc-theorems>