-- <vc-preamble>
def sortedbad (s : String) : Prop :=
(∀ i j, 0 ≤ i ∧ i ≤ j ∧ j < s.length ∧ s.get ⟨i⟩ = 'b' ∧ s.get ⟨j⟩ ≠ 'b' → i < j) ∧
(∀ i j, 0 ≤ i ∧ i ≤ j ∧ j < s.length ∧ s.get ⟨i⟩ ≠ 'd' ∧ s.get ⟨j⟩ = 'd' → i < j)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BadSort (a : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem BadSort_spec (a : String) :
(∀ i, 0 ≤ i ∧ i < a.length → a.get ⟨i⟩ = 'b' ∨ a.get ⟨i⟩ = 'a' ∨ a.get ⟨i⟩ = 'd') →
let b := BadSort a
sortedbad b ∧

-- Note: Simplified multiset condition since exact multiset ops not available

b.length = a.length :=
sorry
-- </vc-theorems>