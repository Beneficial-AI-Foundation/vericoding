-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def filter_words (s : String) : String :=
sorry

def countSubstr (s : String) (sub : String) : Nat :=
sorry

def containsSubstr (s : String) (sub : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem filter_words_output_is_string (s : String) :
  filter_words s = filter_words s :=
sorry

theorem filter_words_idempotent (s : String) :
  filter_words (filter_words s) = filter_words s :=
sorry

theorem filter_words_preserves_other_content (s : String) :
  let banned_pattern := "bad|mean|ugly|horrible|hideous"
  let remove_banned (str : String) := str.replace banned_pattern ""
  remove_banned s = remove_banned (filter_words s) :=
sorry
-- </vc-theorems>