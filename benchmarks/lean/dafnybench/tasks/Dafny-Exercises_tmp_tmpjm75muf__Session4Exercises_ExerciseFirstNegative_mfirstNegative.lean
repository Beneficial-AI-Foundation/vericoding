-- <vc-preamble>
def positive (s : Array Int) : Prop :=
∀ u, 0 ≤ u ∧ u < s.size → s[u]! ≥ 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mfirstNegative (v : Array Int) : Bool × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mfirstNegative_spec (v : Array Int) :
let (b, i) := mfirstNegative v
(b ↔ ∃ k, 0 ≤ k ∧ k < v.size ∧ v[k]! < 0) ∧
(b → 0 ≤ i ∧ i < v.size ∧ v[i.toNat]! < 0 ∧ positive (v.extract 0 i.toNat)) :=
sorry
-- </vc-theorems>