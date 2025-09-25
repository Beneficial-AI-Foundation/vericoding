-- <vc-preamble>
def IsEven (n : Int) : Bool :=
n % 2 = 0

def IsOdd (n : Int) : Bool :=
n % 2 ≠ 0

def IsFirstEven (evenIndex : Nat) (lst : Array Int) : Prop :=
0 ≤ evenIndex ∧ evenIndex < lst.size ∧
IsEven (lst[evenIndex]!) ∧
(∀ i, 0 ≤ i ∧ i < evenIndex → IsOdd (lst[i]!))

def IsFirstOdd (oddIndex : Nat) (lst : Array Int) : Prop :=
0 ≤ oddIndex ∧ oddIndex < lst.size ∧
IsOdd (lst[oddIndex]!) ∧
(∀ i, 0 ≤ i ∧ i < oddIndex → IsEven (lst[i]!))
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FirstEvenOddIndices (lst : Array Int) : Nat × Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FirstEvenOddIndices_spec (lst : Array Int) :
lst.size ≥ 2 →
(∃ i, 0 ≤ i ∧ i < lst.size ∧ IsEven (lst[i]!)) →
(∃ i, 0 ≤ i ∧ i < lst.size ∧ IsOdd (lst[i]!)) →
let (evenIndex, oddIndex) := FirstEvenOddIndices lst
0 ≤ evenIndex ∧ evenIndex < lst.size ∧
0 ≤ oddIndex ∧ oddIndex < lst.size ∧
IsEven (lst[evenIndex]!) ∧ IsFirstEven evenIndex lst ∧
IsOdd (lst[oddIndex]!) ∧ IsFirstOdd oddIndex lst :=
sorry
-- </vc-theorems>