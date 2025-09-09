-- <vc-helpers>
-- </vc-helpers>

def get_note (freq : Float) : String := sorry

def NOTES : List (Float × String) := [
  (440, "A"),
  (466.16, "A#"), 
  (493.88, "B"),
  (523.25, "C"),
  (554.37, "C#"), 
  (587.33, "D"),
  (622.25, "D#"),
  (659.25, "E"), 
  (698.46, "F"),
  (739.99, "F#"),
  (783.99, "G"),
  (830.61, "G#")
]

theorem base_frequencies (freq : Float) (note : String) :
  (freq, note) ∈ NOTES → get_note freq = note := sorry

theorem frequency_multipliers (freq : Float) (note : String) (mult : Float) :
  (freq, note) ∈ NOTES →
  (mult = 0.5 ∨ mult = 2 ∨ mult = 4) →
  get_note (freq * mult) = note := sorry

/-
info: 'A'
-/
-- #guard_msgs in
-- #eval get_note 440

/-
info: 'A'
-/
-- #guard_msgs in
-- #eval get_note 220

/-
info: 'A'
-/
-- #guard_msgs in
-- #eval get_note 880

/-
info: 'C'
-/
-- #guard_msgs in
-- #eval get_note 523.25

/-
info: 'C'
-/
-- #guard_msgs in
-- #eval get_note 261.625

/-
info: 'C'
-/
-- #guard_msgs in
-- #eval get_note 1046.5

-- Apps difficulty: introductory
-- Assurance level: unguarded