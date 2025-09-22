-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def make_sentences (parts : List String) : String := sorry

def stringContains (s : String) (sub : String) : Bool :=
  s.data.asString.contains sub.data[0]! -- simplified for example
-- </vc-definitions>

-- <vc-theorems>
theorem make_sentences_ends_with_period
  (parts : List String) 
  (h : parts.length > 0) :
  (make_sentences parts).endsWith "." := sorry

theorem make_sentences_single_period
  (parts : List String)
  (h : parts.length > 0) :
  ((make_sentences parts).data.filter (· = '.') |>.length) = 1 := sorry

theorem make_sentences_no_trailing_space
  (parts : List String)
  (h : parts.length > 0) :
  ¬((make_sentences parts).dropRight 1).endsWith " " := sorry

theorem make_sentences_comma_space
  (parts : List String)
  (h : parts.length > 0) :
  ((make_sentences parts).data.contains ',') → 
    ((make_sentences parts).data.take ((make_sentences parts).length - 1)).contains ' ' := sorry

theorem make_sentences_preserves_content
  (parts : List String)
  (h : parts.length > 0)
  (part : String)
  (h2 : part ∈ parts)
  (h3 : part ≠ "," ∧ part ≠ ".") :
  (stringContains (make_sentences parts) part) = true := sorry
-- </vc-theorems>