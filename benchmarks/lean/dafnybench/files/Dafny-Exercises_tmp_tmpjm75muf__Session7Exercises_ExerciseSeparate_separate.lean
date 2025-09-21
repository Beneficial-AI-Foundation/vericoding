-- <vc-preamble>
def strictNegative (v : Array Int) (i j : Int) : Prop :=
i ≥ 0 ∧ i ≤ j ∧ j ≤ v.size ∧
∀ u : Nat, i ≤ u ∧ u < j → v[u]! < 0
def positive (s : Array Int) : Prop :=
∀ u : Nat, u < s.size → s[u]! ≥ 0
def isPermutation (s t : Array Int) : Prop :=
s.size = t.size ∧ ∃ p : Nat → Nat, ∀ i : Nat, i < s.size → s[i]! = t[p i]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def separate (v : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem separate_spec (v : Array Int) :
let i := separate v
0 ≤ i ∧ i ≤ v.size ∧
positive (v.extract 0 (Int.toNat i)) ∧
strictNegative v i v.size ∧
isPermutation v (v.extract 0 v.size) :=
sorry
-- </vc-theorems>