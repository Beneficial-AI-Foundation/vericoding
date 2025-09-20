-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def split (s : String) (sep : Char → Bool) : List String :=
sorry

def trim (s : String) : String :=
sorry

def to_freud (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_string_returns_empty :
  to_freud "" = "" :=
sorry

theorem only_whitespace_returns_empty (s : String) :
  trim s = "" → to_freud s = "" :=
sorry

theorem non_empty_only_contains_sex (s : String) :
  trim s ≠ "" →
  List.all (split (to_freud s) (· = ' ')) (· = "sex") :=
sorry

theorem preserves_word_count (s : String) :
  trim s ≠ "" →
  (split (to_freud s) (· = ' ')).length = (split (trim s) (· = ' ')).length :=
sorry
-- </vc-theorems>