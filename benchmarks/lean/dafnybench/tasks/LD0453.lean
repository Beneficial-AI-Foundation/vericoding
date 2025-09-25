-- <vc-preamble>
def sortedbad (s : String) : Prop :=
(∀ i j, 0 ≤ i ∧ i < s.length ∧ 0 ≤ j ∧ j < s.length ∧ s.get ⟨i⟩ = 'b' ∧ (s.get ⟨j⟩ = 'a' ∨ s.get ⟨j⟩ = 'd') → i < j) ∧
(∀ i j, 0 ≤ i ∧ i < s.length ∧ 0 ≤ j ∧ j < s.length ∧ s.get ⟨i⟩ = 'a' ∧ s.get ⟨j⟩ = 'b' → i > j) ∧
(∀ i j, 0 ≤ i ∧ i < s.length ∧ 0 ≤ j ∧ j < s.length ∧ s.get ⟨i⟩ = 'a' ∧ s.get ⟨j⟩ = 'd' → i < j) ∧
(∀ i j, 0 ≤ i ∧ i < s.length ∧ 0 ≤ j ∧ j < s.length ∧ s.get ⟨i⟩ = 'd' ∧ (s.get ⟨j⟩ = 'a' ∨ s.get ⟨j⟩ = 'b') → i > j)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BadSort (a : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem BadSort_spec (a : String) :
(∀ k, 0 ≤ k ∧ k < a.length → (a.get ⟨k⟩ = 'b' ∨ a.get ⟨k⟩ = 'a' ∨ a.get ⟨k⟩ = 'd')) →
let b := BadSort a
sortedbad b ∧
b.length = a.length :=
sorry
-- </vc-theorems>