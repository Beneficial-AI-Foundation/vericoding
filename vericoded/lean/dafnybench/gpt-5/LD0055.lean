import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
noncomputable section
-- LLM HELPER
theorem injective_of_ne (f : Nat → Nat)
  (h : ∀ n1 n2 : Nat, n1 ≠ n2 → f n1 ≠ f n2) : Function.Injective f := by
  classical
  intro a b hfab
  by_contra hne
  exact (h a b hne) hfab
-- </vc-helpers>

-- <vc-definitions>
def convert_map_key (inputs : Nat → Option Bool) (f : Nat → Nat) : Nat → Option Bool :=
fun n => by
  classical
  exact (if h : ∃ k, f k = n then inputs (Nat.find h) else none)
-- </vc-definitions>

-- <vc-theorems>
theorem convert_map_key_spec
(inputs : Nat → Option Bool)
(f : Nat → Nat) :
(∀ n1 n2 : Nat, n1 ≠ n2 → f n1 ≠ f n2) →
(∀ k : Nat, (inputs k).isSome ↔ (convert_map_key inputs f (f k)).isSome) ∧
(∀ k : Nat, (inputs k).isSome → convert_map_key inputs f (f k) = inputs k) :=
by
  classical
  intro inj
  have injF : Function.Injective f := injective_of_ne f inj
  constructor
  · intro k
    have hEx : ∃ k0, f k0 = f k := ⟨k, rfl⟩
    have hk : Nat.find hEx = k := by
      simpa using (injF (Nat.find_spec hEx))
    simpa [convert_map_key, dif_pos hEx, hk]
  · intro k _
    have hEx : ∃ k0, f k0 = f k := ⟨k, rfl⟩
    have hk : Nat.find hEx = k := by
      simpa using (injF (Nat.find_spec hEx))
    simpa [convert_map_key, dif_pos hEx, hk]
end
-- </vc-theorems>
