-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverseWords (s : String) : String := sorry

theorem reverseWords_preserves_length (s : String) :
  (reverseWords s).length = s.length := 
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverseWords_preserves_spaces (s : String) (p : String.Pos) : 
  (s.get p = ' ') ↔ ((reverseWords s).get p = ' ') :=
sorry 

theorem reverseWords_involution (s : String) :
  reverseWords (reverseWords s) = s :=
sorry

theorem reverseWords_reverses_words_individually (s : String) :
  let orig_words := s.split (· = ' ')
  let result_words := (reverseWords s).split (· = ' ')
  orig_words.length = result_words.length ∧ 
  ∀ (i : Fin orig_words.length), 
    orig_words[i]! = String.mk (List.reverse (result_words[i]!).data) :=
sorry
-- </vc-theorems>