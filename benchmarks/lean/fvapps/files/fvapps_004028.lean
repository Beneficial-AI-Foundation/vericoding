-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sha256_cracker (h: String) (chars: String) : Option String :=
  sorry

def sha256 (s: String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem found_string_matches_hash
  {s h chars result: String} :
  (h = sha256 s) →
  (chars = s.toList.toString) →
  (sha256_cracker h chars = some result) →
  (sha256 result = h) ∧
  (∀ c, c ∈ result.data → c ∈ chars.data) :=
sorry

theorem invalid_chars_return_none
  {s h invalid_chars chars: String} :
  (h = sha256 s) →
  (chars = (invalid_chars.toList.filter (fun c => !s.data.contains c)).toString) →
  (chars ≠ "") →
  sha256_cracker h chars = none :=
sorry

theorem empty_chars_returns_none
  {s h: String} :
  (h = sha256 s) →
  sha256_cracker h "" = none :=
sorry
-- </vc-theorems>