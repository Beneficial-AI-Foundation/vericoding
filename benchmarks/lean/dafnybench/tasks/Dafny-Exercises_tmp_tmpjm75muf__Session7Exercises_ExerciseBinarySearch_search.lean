-- <vc-preamble>
def sorted (s : Array Int) : Prop :=
∀ u w : Nat, u < w → w < s.size → s[u]! ≤ s[w]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binarySearch (v : Array Int) (elem : Int) : Int :=
sorry

def search (v : Array Int) (elem : Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem binarySearch_spec (v : Array Int) (elem : Int) :
sorted v →
0 ≤ binarySearch v elem →
(∀ u : Nat, u ≤ Int.toNat (binarySearch v elem) ∧ u < v.size → v[u]! ≤ elem) ∧
(∀ w : Nat, Int.toNat (binarySearch v elem) < w ∧ w < v.size → v[w]! > elem) :=
sorry

theorem search_spec (v : Array Int) (elem : Int) :
sorted v →
search v elem = true ↔ (∃ i, 0 ≤ i ∧ i < v.size ∧ v[i]! = elem) :=
sorry
-- </vc-theorems>