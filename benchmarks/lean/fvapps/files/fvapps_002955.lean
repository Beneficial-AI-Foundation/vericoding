-- <vc-preamble>
def isOrdered (s : List Char) : Prop :=
  ∀ i j, i < j → j < s.length → s[i]! ≤ s[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_alpha (c : Char) : Bool := sorry

def scramble_words (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem scramble_length_preserved (s : String) :
  String.length (scramble_words s) = String.length s :=
sorry

theorem first_last_letters_preserved (s : String) (word : String) (h : word.length > 1)
    (pos_start : String.Pos) (pos_end : String.Pos) :
  is_alpha (word.get pos_start) →
  is_alpha (word.get pos_end) →
  (scramble_words word).get pos_start = word.get pos_start ∧
  (scramble_words word).get pos_end = word.get pos_end :=
sorry

theorem middle_chars_sorted (s : String) (h : s.length > 2)
    (pos_start : String.Pos) (pos_end : String.Pos) :
  is_alpha (s.get pos_start) →
  is_alpha (s.get pos_end) →
  let middle := (scramble_words s).data.drop 1 |>.take (s.length - 2)
  isOrdered middle :=
sorry

theorem non_alpha_chars_preserved (s : String) :
  s.data.filter (fun c => ¬(is_alpha c)) =
  (scramble_words s).data.filter (fun c => ¬(is_alpha c)) :=
sorry
-- </vc-theorems>