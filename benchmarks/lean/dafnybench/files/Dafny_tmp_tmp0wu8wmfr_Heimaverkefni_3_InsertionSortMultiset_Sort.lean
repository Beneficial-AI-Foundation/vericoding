-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Search (s : Array Int) (x : Int) : Int :=
sorry

def sort (m : List Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Search_spec (s : Array Int) (x : Int) (k : Int) :
(∀ p q : Nat, p < q ∧ q < s.size → s[p]! ≤ s[q]!) →
(0 ≤ k ∧ k ≤ s.size) ∧
(∀ i : Nat, i < k.toNat → s[i]! ≤ x) ∧
(∀ i : Nat, k.toNat ≤ i ∧ i < s.size → s[i]! ≥ x) :=
sorry

theorem Sort_spec (m : List Int) (r : Array Int) :
(∀ x : Int, x ∈ m → (∃ i : Nat, i < r.size ∧ r[i]! = x)) ∧
(∀ i : Nat, i < r.size → r[i]! ∈ m) ∧
(∀ p q : Nat, p < q ∧ q < r.size → r[p]! ≤ r[q]!) :=
sorry
-- </vc-theorems>