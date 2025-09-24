-- <vc-preamble>
def IsOdd (x : Int) : Bool :=
x % 2 ≠ 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FindFirstOdd (a : Array Int) : Bool × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FindFirstOdd_spec (a : Array Int) (result : Bool × Int) :
let (found, index) := result
(¬found → ∀ i, 0 ≤ i ∧ i < a.size → ¬IsOdd (a[i]!)) ∧
(found → 0 ≤ index ∧ index < a.size ∧
IsOdd (a[index.toNat]!) ∧
∀ i:Nat, 0 ≤ i ∧ i < index → ¬IsOdd (a[i]!)) :=
sorry
-- </vc-theorems>