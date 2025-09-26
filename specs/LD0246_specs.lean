-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MinOfMultiset (m : List Int) : Int :=
sorry

def sortList (m : List Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem MinOfMultiset_spec (m : List Int) :
let min := MinOfMultiset m
(min ∈ m) ∧
(∀ z, z ∈ m → min ≤ z) :=
sorry

theorem Sort_spec (m : List Int) :
let s := sortList m
(∀ x : Int, x ∈ m → (∃ i : Nat, i < s.size ∧ s[i]! = x)) ∧
(∀ i : Nat, i < s.size → s[i]! ∈ m) ∧
(∀ p q : Nat, p < q ∧ q < s.size → s[p]! ≤ s[q]!) :=
sorry
-- </vc-theorems>