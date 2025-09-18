-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def add_binary (a b : Nat) : String := sorry

theorem add_binary_matches_built_in 
  (a b : Nat) : 
  add_binary a b = toString (Nat.toDigits 2 (a + b)) := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem add_binary_is_valid_binary
  (a b : Nat) : 
  add_binary a b = toString (Nat.toDigits 2 (a + b)) ∧
  ∃ n : Nat, toString n = add_binary a b :=
  sorry

theorem add_binary_with_zero
  (n : Nat) :
  add_binary n 0 = toString (Nat.toDigits 2 n) ∧
  add_binary 0 n = toString (Nat.toDigits 2 n) :=
  sorry
-- </vc-theorems>