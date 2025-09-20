-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def omit_hashtag (message : String) (hashtag : String) : String :=
sorry

def String.count (s t : String) : Nat :=
sorry

def String.containsSubstring (s t : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem omit_hashtag_length (message hashtag : String) :
  String.length (omit_hashtag message hashtag) ≤ String.length message :=
sorry

theorem omit_hashtag_unchanged (message hashtag : String) :
  ¬(String.containsSubstring message hashtag) → omit_hashtag message hashtag = message :=
sorry

theorem omit_hashtag_count (message hashtag : String) (h1 : hashtag ≠ "")
  (h2 : String.count message hashtag > 1) :
  String.count (omit_hashtag message hashtag) hashtag = String.count message hashtag - 1 :=
sorry

theorem omit_empty_hashtag (message : String) :
  omit_hashtag message "" = message :=
sorry

theorem omit_from_empty_message (hashtag : String) (h1 : hashtag ≠ "") :
  omit_hashtag "" hashtag = "" :=
sorry

theorem omit_hashtag_not_found (message hashtag : String)
  (h1 : message ≠ "") (h2 : hashtag ≠ "") :
  ¬(String.containsSubstring message hashtag) → omit_hashtag message hashtag = message :=
sorry
-- </vc-theorems>