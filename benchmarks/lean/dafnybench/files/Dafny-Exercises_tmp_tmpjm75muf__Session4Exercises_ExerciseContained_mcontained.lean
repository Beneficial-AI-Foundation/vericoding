-- <vc-preamble>
def strictSorted (s : Array Int) : Prop :=
∀ u w, 0 ≤ u → u < w → w < s.size → s[u]! < s[w]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mcontained (v w : Array Int) (n m : Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mcontained_spec (v w : Array Int) (n m : Int) :
n ≤ m ∧
n ≥ 0 ∧
strictSorted v ∧
strictSorted w ∧
v.size ≥ n ∧
w.size ≥ m →
mcontained v w n m = (∀ k, 0 ≤ k ∧ k < n → ∃ j, 0 ≤ j ∧ j < m ∧ v[k.toNat]! = w[j.toNat]!) :=
sorry
-- </vc-theorems>