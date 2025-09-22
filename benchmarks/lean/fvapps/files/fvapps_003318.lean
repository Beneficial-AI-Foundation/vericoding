-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPP (n : Nat) : Option (Nat × Nat) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isPP_properties {n : Nat} (h : n > 0) :
  match isPP n with
  | none => 
    ∀ b e, b ≥ 2 → e ≥ 2 → b ^ e ≠ n
  | some (b, e) =>
    b ≥ 2 ∧ e ≥ 2 ∧ b ^ e = n
  := sorry

theorem isPP_perfect_powers {base exp : Nat} 
  (hbase : base ≥ 2) (hexp : exp ≥ 2) :
  ∃ b e, 
    isPP (base ^ exp) = some (b, e) ∧
    b ^ e = base ^ exp
  := sorry
-- </vc-theorems>