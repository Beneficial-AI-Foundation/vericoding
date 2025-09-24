-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def substring (s : String) : String := sorry

theorem substring_empty_or_single_char (s : String) :
  let result := substring s
  (s = "" → result = "") ∧ result.length ≤ s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem substring_at_most_two_unique_chars (s : String) :
  s ≠ "" →
  let result := substring s
  let chars := result.data
  chars.eraseDups.length ≤ 2 := sorry

theorem substring_is_contiguous (s : String) :
  let result := substring s
  result ≠ "" →
  ∃ start len, (s.drop start).take len = result := sorry

theorem substring_is_maximal (s : String) :
  let result := substring s
  ∀ start len,
    let candidate := (s.drop start).take len
    let candidateChars := candidate.data
    candidateChars.eraseDups.length ≤ 2 →
    candidate.length ≤ result.length := sorry

theorem two_char_string_returns_full (s : String) :
  s ≠ "" →
  (∀ c ∈ s.data, c = 'a' ∨ c = 'b') →
  substring s = s := sorry
-- </vc-theorems>