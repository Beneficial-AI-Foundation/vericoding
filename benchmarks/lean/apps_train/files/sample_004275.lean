Your task is to validate rhythm with a meter.

_________________________________________________
Rules:

1. Rhythmic division requires that in one whole note (1) there are two half notes (2) or four quarter notes (4) or eight eighth notes (8). 
Examples: 1 = 2 + 2, 1 = 4 + 4 + 4 + 4 ... 
Note that: 2 = 4 + 4, 4 = 8 + 8, 2 = 8 + 8 + 4 ... 

2. Meter gives an information how many rhythmic types of notes should be in one bar. Bar is the the primary section of a musical score.
Examples: 
          4/4 -> 4 quarter notes in a bar
          5/2 -> 5 half notes in a bar
          3/8 -> 3 eighth notes in a bar
Note that: 
for 4/4 valid bars are: '4444', '88888888', '2488' ...
for 5/2 valid bars are: '22222', '2244244', '8888244888844' ...
for 3/8 valid bars are: '888', '48' ...

3. Anacrusis occurs when all bars but the first and last are valid, and the notes in the first and last bars when combined would also make a valid bar.

Examples: 
for 4/4 valid anacrusis is -> 44|...|44 or 88|...|888888 or 2|...|488 
for 5/2 valid anacrusis is -> 22|...|222 or 222|...|22 or  2244|...|244
for 3/8 valid anacrusis is -> 8|...|88 or 4|...|8 or 8|...|4
Note:
When anacrusis is valid but other bars in score are not -> return 'Invalid rhythm'
________________________________________________

Input:
meter - array: eg. [4, 4],
score - string, bars separated with '|': eg. '4444|8484842|888'

Output:
string message: 'Valid rhythm', 'Valid rhythm with anacrusis' or 'Invalid rhythm'

def IsPowerOfTwo (n : Nat) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded