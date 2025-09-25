-- <vc-preamble>
def sorted (s : Array Int) : Prop :=
∀ u w : Nat, u < w → w < s.size → s[u]! ≤ s[w]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binarySearch (v : Array Int) (elem : Int) : Int :=
sorry

def otherbSearch (v : Array Int) (elem : Int) : Bool × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem binarySearch_spec (v : Array Int) (elem : Int) :
sorted v →
0 ≤ binarySearch v elem →
(∀ u : Nat, u ≤ Int.toNat (binarySearch v elem) ∧ u < v.size → v[u]! ≤ elem) ∧
(∀ w : Nat, Int.toNat (binarySearch v elem) < w ∧ w < v.size → v[w]! > elem) :=
sorry

theorem otherbSearch_spec (v : Array Int) (elem : Int) :
sorted v →
let (b, p) := otherbSearch v elem
0 ≤ p ∧ p ≤ v.size ∧
(b ↔ ∃ i, 0 ≤ i ∧ i < v.size ∧ v[i]! = elem) ∧
(b → p < v.size ∧ v[p.toNat]! = elem) ∧
(¬b → (∀ u, 0 ≤ u ∧ u < p → v[u.toNat]! < elem) ∧
(∀ w, p ≤ w ∧ w < v.size → v[w.toNat]! > elem)) :=
sorry
-- </vc-theorems>