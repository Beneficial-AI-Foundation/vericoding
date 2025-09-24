-- <vc-preamble>
def get_hint (secret: String) (guess: String) : String :=
  sorry

def countMatches (s1 s2: String) : Nat :=
  sorry

def natToString (n: Nat) : String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def splitHint (hint: String) : HintResult :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hint_format {secret guess: String} (h: secret.length = guess.length):
  let hint := get_hint secret guess 
  let bulls_cows := hint.dropRight 1
  let parts := bulls_cows.split (λc => c = 'A')
  (hint.takeRight 1 = "B" ∧ 
   parts.length = 2 ∧
   parts[0]!.all Char.isDigit ∧
   parts[1]!.all Char.isDigit)
  := sorry

theorem hint_counts_valid {secret guess : String} (h: secret.length = guess.length):
  let hint := get_hint secret guess
  let result := splitHint hint
  (result.bulls + result.cows ≤ secret.length ∧
   result.bulls ≤ countMatches secret guess)
  := sorry

theorem identical_strings_hint {s : String}:
  get_hint s s = natToString s.length ++ "A0B"
  := sorry

theorem hint_symmetry {secret guess : String} (h: secret.length = guess.length):
  let hint1 := get_hint secret guess
  let hint2 := get_hint guess secret
  (splitHint hint1).bulls = (splitHint hint2).bulls
  := sorry

/-
info: '1A3B'
-/
-- #guard_msgs in
-- #eval get_hint "1807" "7810"

/-
info: '1A1B'
-/
-- #guard_msgs in
-- #eval get_hint "1123" "0111"

/-
info: '0A0B'
-/
-- #guard_msgs in
-- #eval get_hint "1234" "5678"
-- </vc-theorems>