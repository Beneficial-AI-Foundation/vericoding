-- <vc-preamble>
def count_hashtags (s : String) : Nat :=
  s.foldl (fun acc c => if c = '#' then acc + 1 else acc) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def clean_string (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem clean_string_idempotent (s : String) :
  clean_string (clean_string s) = clean_string s :=
sorry

theorem clean_string_no_hashtags (s : String) :
  ¬(String.contains (clean_string s) '#') :=
sorry

theorem clean_string_append {s₁ s₂ : String}
  (h₁ : ¬(String.contains s₁ '#'))
  (h₂ : ¬(String.contains s₂ '#')) :
  clean_string (s₁ ++ s₂) = clean_string s₁ ++ clean_string s₂ :=
sorry

theorem clean_string_length (s : String) :
  String.length (clean_string s) ≤ String.length s - count_hashtags s :=
sorry

theorem clean_string_empty :
  clean_string "" = "" :=
sorry
-- </vc-theorems>