-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def format_words (words : List String) : String :=
sorry

def String.countSubstr (s1 s2 : String) : Nat :=
sorry

def substringExists (s1 s2 : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem format_words_empty_filtered :
  ∀ (words : List String),
  (words.filter (fun w => w ≠ "")).isEmpty →
  format_words words = "" :=
sorry

theorem format_words_contains_filtered :
  ∀ (words : List String) (word : String),
  word ≠ "" →
  word ∈ words →
  substringExists (format_words words) word = true :=
sorry

theorem format_words_single_and :
  ∀ (words : List String),
  (words.filter (fun w => w ≠ "")).length > 1 →
  substringExists (format_words words) " and " = true ∧
  String.countSubstr (format_words words) " and " = 1 :=
sorry

theorem format_words_no_and :
  ∀ (words : List String),
  (words.filter (fun w => w ≠ "")).length ≤ 1 →
  substringExists (format_words words) "and" = false :=
sorry

theorem format_words_maintains_order :
  ∀ (words : List String),
  ¬(words.filter (fun w => w ≠ "")).isEmpty →
  let filtered := words.filter (fun w => w ≠ "")
  substringExists (format_words words) filtered.head! ∧
  substringExists (format_words words) filtered.getLast! ∧
  format_words words = filtered.head! ∨
  format_words words = filtered.head! ++ ", " ++ filtered.getLast! ∨
  format_words words = filtered.head! ++ " and " ++ filtered.getLast! :=
sorry
-- </vc-theorems>