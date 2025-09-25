-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_it (s : String) (n : Nat) : String :=
sorry

def isCharNSorted (words : List String) (n : Nat) : Bool :=
sorry

def sameSets (s1 : List String) (s2 : List String) : Bool :=
sorry

def wordsFromString (s : String) : List String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_it_preserves_words (s : String) (n : Nat) :
  n > 0 → sameSets (wordsFromString s) (wordsFromString (sort_it s n)) :=
sorry

theorem sort_it_is_n_sorted (s : String) (n : Nat) (h : n > 0) :
  isCharNSorted (wordsFromString (sort_it s n)) n :=
sorry

theorem sort_it_first_char_is_normal_sort (s : String) :
  sort_it s 1 = String.intercalate ", " (wordsFromString s) :=
sorry
-- </vc-theorems>