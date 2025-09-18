-- <vc-preamble>
def NoteNames : List String := ["C", "C#", "Db", "D", "D#", "Eb", "E", "F", "F#", "Gb", "G", "G#", "Ab", "A", "A#", "Bb", "B"]

/- The main function that determines if a chord is major, minor, or invalid -/

def minor_or_major (input : String) : String := sorry

/- Returns the list of words in a string -/
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def splitString (s : String) : List String := sorry

/- Invalid input types should return "Not a chord" -/
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_input_numeric (n : Nat) :
  minor_or_major (toString n) = "Not a chord" := sorry
-- </vc-theorems>