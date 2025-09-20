-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toString (s : List Char) : String :=
sorry

def capitalize_name (s : String) : String :=
sorry

def splitOn (s : String) (p : Char → Bool) : List String :=
sorry

def front (s : String) : Char :=
sorry

def drop (s : String) (n : Nat) : String :=
sorry

def isAlpha (c : Char) : Bool :=
sorry

def isUpper (c : Char) : Bool :=
sorry

def toLower (s : String) : String :=
sorry

def length (s : String) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem capitalize_name_preserves_word_count (s : String) :
  (splitOn (capitalize_name s) (fun x => x = ' ')).length =
  (splitOn s (fun x => x = ' ')).length :=
sorry

theorem words_start_with_uppercase (s : String) (word : String) :
  word ∈ splitOn (capitalize_name s) (fun x => x = ' ') →
  word.length > 0 →
  isAlpha (word.front) →
  isUpper (word.front) ∧ word.drop 1 = toLower (word.drop 1) :=
sorry

theorem whitespace_only_preserves_length (s : String) :
  (∀ c ∈ s.data, c = ' ') →
  (splitOn (capitalize_name s) (fun x => x = ' ')).length =
  (splitOn s (fun x => x = ' ')).length :=
sorry

theorem non_alpha_preserved (s : String) :
  (∀ c ∈ s.data, !isAlpha c) →
  s.length > 0 →
  capitalize_name s = s :=
sorry
-- </vc-theorems>