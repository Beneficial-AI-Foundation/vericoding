-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_yalalovichik_substrings (s: String) : Nat :=
  sorry

def longest_run (s: String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_always_nonnegative (s: String) (h: s.length > 0):
  count_yalalovichik_substrings s ≥ 0 :=
sorry

theorem single_char_count (c: Char):
  count_yalalovichik_substrings (String.singleton c) = 1 :=
sorry

theorem repeated_single_char (n: Nat) (h: n > 0):
  let s := String.join (List.replicate n "a")
  count_yalalovichik_substrings s = n :=
sorry

theorem alternating_chars (n: Nat) (h: n > 0):
  let s := String.join (List.replicate n "ab")
  count_yalalovichik_substrings s = 2 :=
sorry
-- </vc-theorems>