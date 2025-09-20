-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def levenshtein (s1 s2 : String) : Nat :=
  sorry

def repeatChar (c : Char) (n : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem levenshtein_nonneg (s1 s2 : String) :
  levenshtein s1 s2 ≥ 0 :=
sorry

theorem levenshtein_identity (s : String) :
  levenshtein s s = 0 :=
sorry

theorem levenshtein_symm (s1 s2 : String) :
  levenshtein s1 s2 = levenshtein s2 s1 :=
sorry

theorem levenshtein_triangle (s1 s2 s3 : String) :
  levenshtein s1 s2 ≤ levenshtein s1 s3 + levenshtein s3 s2 :=
sorry

theorem levenshtein_empty_string (s : String) :
  levenshtein s "" = s.length :=
sorry

theorem levenshtein_empty_string_rev (s : String) :
  levenshtein "" s = s.length :=
sorry
-- </vc-theorems>