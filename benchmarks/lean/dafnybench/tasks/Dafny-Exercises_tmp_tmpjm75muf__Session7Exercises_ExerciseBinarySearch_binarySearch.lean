-- <vc-preamble>
def sorted (s : Array Int) : Prop :=
∀ u w : Nat, u < w → w < s.size → s[u]! ≤ s[w]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binarySearch (v : Array Int) (elem : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem binarySearch_spec (v : Array Int) (elem : Int) :
sorted v →
0 ≤ binarySearch v elem →
(∀ u : Nat, u ≤ Int.toNat (binarySearch v elem) ∧ u < v.size → v[u]! ≤ elem) ∧
(∀ w : Nat, Int.toNat (binarySearch v elem) < w ∧ w < v.size → v[w]! > elem) :=
sorry
-- </vc-theorems>