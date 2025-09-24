-- <vc-preamble>
def SetLessThan (numbers : List Int) (threshold : Int) : List Int :=
numbers.filter (λ x => x < threshold)

def seqSet (nums : Array Int) (index : Nat) : List Int :=
(List.range index).map (λ i => nums[i]!)

def SortedSeq (a : Array Int) : Prop :=
∀ i j, 0 ≤ i → i < j → j < a.size → a[i]! < a[j]!

def sorted (a : Array Int) : Prop :=
∀ i j, 0 ≤ i → i < j → j < a.size → a[i]! < a[j]!

def distinct (a : Array Int) : Prop :=
∀ i j, 0 ≤ i → i < a.size → 0 ≤ j → j < a.size → i ≠ j → a[i]! ≠ a[j]!

def sorted_eq (a : Array Int) : Prop :=
∀ i j, 0 ≤ i → i < j → j < a.size → a[i]! ≤ a[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def GetInsertIndex (a : Array Int) (limit : Int) (x : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem GetInsertIndex_spec (a : Array Int) (limit : Int) (x : Int) (idx : Int) :
(∀ i, 0 ≤ i → i < a.size → a[i]! ≠ x) →
0 ≤ limit → limit ≤ a.size →
SortedSeq (a.extract 0 limit.toNat) →
0 ≤ idx ∧ idx ≤ limit ∧
SortedSeq (a.extract 0 limit.toNat) ∧
(idx > 0 → a[(idx - 1).toNat]! < x) ∧
(idx < limit → x < a[(idx).toNat]!) :=
sorry
-- </vc-theorems>