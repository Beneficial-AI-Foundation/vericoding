-- <vc-preamble>
def triple (a : Array Int) : Prop :=
∃ i, 0 ≤ i ∧ i < a.size - 2 ∧ a[i]! = a[(i + 1)]! ∧ a[(i + 1)]! = a[(i + 2)]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def GetTriple (a : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem GetTriple_spec (a : Array Int) :
let index := GetTriple a
(0 ≤ index ∧ index < a.size - 2 ∨ index = a.size) ∧
(index = a.size ↔ ¬(triple a)) ∧
(0 ≤ index ∧ index < a.size - 2 ↔ triple a) ∧
(0 ≤ index ∧ index < a.size - 2 →
a[index.toNat]! = a[(index + 1).toNat]! ∧ a[(index + 1).toNat]! = a[(index + 2).toNat]!) :=
sorry
-- </vc-theorems>