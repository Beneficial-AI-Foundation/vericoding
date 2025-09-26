-- <vc-preamble>
def sorted (s : Array Int) : Prop :=
∀ u w : Nat, u < w → w < s.size → s[u]! ≤ s[w]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binarySearchRec (v : Array Int) (elem : Int) (c : Int) (f : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem binarySearchRec_spec
(v : Array Int) (elem : Int) (c : Int) (f : Int) :
sorted (v.extract 0 v.size) →
0 ≤ c → c ≤ f + 1 → f + 1 ≤ v.size →
(∀ k : Nat, k < c.toNat → v[k]! ≤ elem) →
(∀ k : Nat, f.toNat < k → k < v.size → v[k]! > elem) →
-1 ≤ binarySearchRec v elem c f ∧ binarySearchRec v elem c f < v.size ∧
(∀ u : Nat, u ≤ Int.toNat (binarySearchRec v elem c f) ∧ u < v.size → v[u]! ≤ elem) ∧
(∀ w : Nat, Int.toNat (binarySearchRec v elem c f) < w ∧ w < v.size → v[w]! > elem) :=
sorry
-- </vc-theorems>