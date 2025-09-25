-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def StringSwap (s : String) (i j : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem StringSwap_spec (s : String) (i j : Nat) :
i ≥ 0 ∧ j ≥ 0 ∧ s.length ≥ 0 →
(s.length > 0 → i < s.length ∧ j < s.length) →
let t := StringSwap s i j
(s.length = t.length) ∧
(s.length > 0 →
(∀ k : Nat, k ≠ i ∧ k ≠ j ∧ k < s.length → t.get ⟨k⟩ = s.get ⟨k⟩) ∧
t.get ⟨i⟩ = s.get ⟨j⟩ ∧ t.get ⟨j⟩ = s.get ⟨i⟩) ∧
(s.length = 0 → t = s) :=
sorry
-- </vc-theorems>