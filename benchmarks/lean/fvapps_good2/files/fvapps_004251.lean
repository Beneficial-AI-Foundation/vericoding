-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def HQ9 (s : String) : Option String :=
  sorry

def contains (haystack needle : String) : Bool :=
  sorry

def count (haystack needle : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hq9_invalid_none :
  HQ9 "" = none ∧ HQ9 " " = none :=
sorry

theorem h_returns_hello :
  HQ9 "H" = some "Hello World!" :=
sorry

theorem q_returns_q :
  HQ9 "Q" = some "Q" :=
sorry

theorem nine_returns_song (result : String) :
  HQ9 "9" = some result →
  contains result "99 bottles of beer" = true ∧
  contains result "1 bottle of beer" = true ∧
  contains (String.toLower result) "no more bottles of beer" = true ∧
  count result "of beer" ≥ 190 ∧
  count result "\n" ≥ 99 :=
sorry

theorem non_hq9_returns_none (s : String) :
  s ≠ "H" → s ≠ "Q" → s ≠ "9" →
  HQ9 s = none :=
sorry
-- </vc-theorems>