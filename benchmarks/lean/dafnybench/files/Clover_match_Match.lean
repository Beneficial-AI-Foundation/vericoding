-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Match (s p : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Match_spec (s p : String) :
s.length = p.length →
Match s p = (∀ n, 0 ≤ n ∧ n < s.length →
(s.get ⟨n⟩ = p.get ⟨n⟩ ∨ p.get ⟨n⟩ = '?')) :=
sorry
-- </vc-theorems>