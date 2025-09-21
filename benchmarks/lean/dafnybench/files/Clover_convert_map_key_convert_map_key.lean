-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def convert_map_key (inputs : Nat → Option Bool) (f : Nat → Nat) : Nat → Option Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem convert_map_key_spec
(inputs : Nat → Option Bool)
(f : Nat → Nat) :
(∀ n1 n2 : Nat, n1 ≠ n2 → f n1 ≠ f n2) →
(∀ k : Nat, (inputs k).isSome ↔ (convert_map_key inputs f (f k)).isSome) ∧
(∀ k : Nat, (inputs k).isSome → convert_map_key inputs f (f k) = inputs k) :=
sorry
-- </vc-theorems>