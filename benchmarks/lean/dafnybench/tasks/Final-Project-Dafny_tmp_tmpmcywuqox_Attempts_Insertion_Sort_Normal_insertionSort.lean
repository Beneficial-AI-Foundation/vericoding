-- <vc-preamble>
def sortedA (a : Array Int) (i : Nat) : Prop :=
∀ k, 0 < k ∧ k < i → a[k-1]! ≤ a[k]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sorted (a : Array Int) : Bool :=
sorry

def lookForMin (a : Array Int) (i : Int) : Int :=
sorry

def insertionSort (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lookForMin_spec (a : Array Int) (i : Nat) :
0 ≤ i ∧ i < a.size →
let m := lookForMin a i
i ≤ m ∧ m < a.size ∧
(∀ k, i ≤ k ∧ k < a.size → a[k]!  ≥ a[m.toNat]!) :=
sorry

theorem insertionSort_spec (a : Array Int) :
sorted (insertionSort a) :=
sorry
-- </vc-theorems>