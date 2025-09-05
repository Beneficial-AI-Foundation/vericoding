Check if given chord is minor or major.

_____________________________________________________________
Rules:

1. Basic minor/major chord have three elements.

2. Chord is minor when interval between first and second element equals 3 and between second and third -> 4.

3. Chord is major when interval between first and second element equals 4 and between second and third -> 3.

4. In minor/major chord interval between first and third element equals... 7.

_______________________________________________________________
There is a preloaded list of the 12 notes of a chromatic scale built on C. This means that there are (almost) all allowed note' s names in music.

notes = 
['C', ['C#', 'Db'], 'D', ['D#', 'Eb'], 'E', 'F', ['F#', 'Gb'], 'G', ['G#', 'Ab'], 'A', ['A#', 'Bb'], 'B']

Note that e. g. 'C#' - 'C' = 1, 'C' - 'C#' = 1, 'Db' - 'C' = 1 and 'B' - 'C' = 1. 

Input:
String of notes separated by whitespace, e. g. 'A C# E'

Output:
String message: 'Minor', 'Major' or 'Not a chord'.

def NoteNames : List String := ["C", "C#", "Db", "D", "D#", "Eb", "E", "F", "F#", "Gb", "G", "G#", "Ab", "A", "A#", "Bb", "B"]

/-- The main function that determines if a chord is major, minor, or invalid -/

def minor_or_major (input : String) : String := sorry

/-- Returns the list of words in a string -/

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded