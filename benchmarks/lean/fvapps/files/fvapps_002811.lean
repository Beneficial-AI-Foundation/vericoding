-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numericals (s : String) : String := sorry

theorem numericals_length_matches_input (s : String) :
  String.length (numericals s) = String.length s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numericals_only_contains_digits (s : String) :
  ∀ p : String.Pos, ((numericals s).get p).isDigit := sorry

theorem numericals_monotonic_repeated_chars (s : String) (c : Char) :
  ∀ i j : String.Pos, i < j → 
  (s.get i = c ∧ s.get j = c) → 
  ((numericals s).get i).toNat ≤ ((numericals s).get j).toNat := sorry

theorem numericals_starts_with_one {s : String} (h : s ≠ "") :
  ∃ p : String.Pos, (numericals s).get p = '1' := sorry
-- </vc-theorems>