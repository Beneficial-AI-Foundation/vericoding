-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SlopeSearch (a : Array (Array Int)) (key : Int) : Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SlopeSearch_spec (a : Array (Array Int)) (key : Int) :
(∀ i j j', 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < j' ∧ j' < a[i]!.size →
a[i]![j]! ≤ a[i]![j']!) →
(∀ i i' j, 0 ≤ i ∧ i < i' ∧ i' < a.size ∧ 0 ≤ j ∧ j < a[i]!.size →
a[i]![j]! ≤ a[i']![j]!) →
(∃ i j, 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < a[i]!.size ∧ a[i]![j]! = key) →
let (m, n) := SlopeSearch a key
0 ≤ m ∧ m < a.size ∧ 0 ≤ n ∧ n < a[m.natAbs]!.size ∧ a[m.natAbs]![n.natAbs]! = key :=
sorry
-- </vc-theorems>