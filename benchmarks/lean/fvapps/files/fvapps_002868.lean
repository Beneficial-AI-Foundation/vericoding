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

/- Wrong number of notes (not equal to 3) should return "Not a chord" -/

theorem wrong_note_count (notes : String) :
  (splitString notes).length ≠ 3 → minor_or_major notes = "Not a chord" := sorry

/- Invalid note names should return "Not a chord" -/

theorem invalid_note_names (notes : String) :
  (∃ note, note ∈ splitString notes ∧ note ∉ NoteNames) → 
  minor_or_major notes = "Not a chord" := sorry

/- Known major chords should return "Major" -/

theorem known_major_chords :
  minor_or_major "C E G" = "Major" ∧
  minor_or_major "F# A# C#" = "Major" := sorry

/- Known minor chords should return "Minor" -/

theorem known_minor_chords :
  minor_or_major "C Eb G" = "Minor" ∧
  minor_or_major "F# A C#" = "Minor" := sorry

/- Enharmonic equivalents should produce the same result -/

theorem enharmonic_equivalence (n1 n2 : String) (other1 other2 : String) :
  ((n1 = "C#" ∧ n2 = "Db") ∨ 
   (n1 = "D#" ∧ n2 = "Eb") ∨
   (n1 = "F#" ∧ n2 = "Gb") ∨
   (n1 = "G#" ∧ n2 = "Ab") ∨
   (n1 = "A#" ∧ n2 = "Bb")) →
  minor_or_major (s!"{n1} {other1} {other2}") = 
  minor_or_major (s!"{n2} {other1} {other2}") := sorry

/-
info: 'Major'
-/
-- #guard_msgs in
-- #eval minor_or_major "C E G"

/-
info: 'Minor'
-/
-- #guard_msgs in
-- #eval minor_or_major "C Eb G"

/-
info: 'Not a chord'
-/
-- #guard_msgs in
-- #eval minor_or_major "C D G"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded