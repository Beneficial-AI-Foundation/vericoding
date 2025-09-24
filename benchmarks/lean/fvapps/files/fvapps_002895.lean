-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def thue_morse (n : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem thue_morse_length (n : Nat) :
  (thue_morse n).length = n ∧
  ∀ p : String.Pos,
    String.contains "01" ((thue_morse n).get p) :=
sorry

theorem thue_morse_prefix_consistency (n : Nat) :
  (thue_morse (n + 1)).take n = thue_morse n :=
sorry

theorem thue_morse_starts_correct (n : Nat) (h : n > 0) :
  ∃ p : String.Pos, (thue_morse n).get p = '0' :=
sorry
-- </vc-theorems>