-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def backspace_compare (s1: String) (s2: String) : Bool :=
  sorry

def normalize_backspace (s: String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem backspace_compare_matches_naive (s1 s2: String) :
  backspace_compare s1 s2 = (normalize_backspace s1 = normalize_backspace s2) :=
by
sorry

theorem self_compare (s: String) :
  backspace_compare s s = true :=
by
sorry

theorem symmetric (s1 s2: String) :
  backspace_compare s1 s2 = backspace_compare s2 s1 :=
by
sorry
-- </vc-theorems>