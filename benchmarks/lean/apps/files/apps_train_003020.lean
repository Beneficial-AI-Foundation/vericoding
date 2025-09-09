-- <vc-helpers>
-- </vc-helpers>

def isAsciiLetter (c : Char) : Bool := sorry

def peteTalk (s : String) (okWords : List String := []) : String := sorry

theorem pete_talk_preserves_pattern {s : String} (word : String)
    (h1 : word ∈ (peteTalk s).split (· = ' '))
    (h2 : word.length > 2)
    (h3 : ∃ c, c ∈ word.data ∧ c = '*') :
    word.front ≠ '*' ∧
    word.back ≠ '*' ∧
    ∀ (i : String.Pos), 1 < i.1 → i.1 < word.length - 1 → word.get i = '*' := sorry

theorem pete_talk_respects_ok_words {s : String} {okWords : List String}
    (word : String)
    (h1 : word ∈ okWords)
    (h2 : word.toLower ∈ s.toLower.split (· = ' ')) :
    word.toLower ∈ (peteTalk s okWords).toLower.split (· = ' ') := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded