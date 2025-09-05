In genetics, a sequence’s motif is a nucleotides (or amino-acid) sequence pattern. Sequence motifs have a biological significance. For more information you can take a look [here](https://en.wikipedia.org/wiki/Sequence_motif).

For this kata you need to complete the function `motif_locator`. This function receives 2 arguments - a sequence and a motif. Both arguments are strings.

You should return an array that contains all the start positions of the motif (in order). A sequence may contain 0 or more repetitions of the given motif. Note that the number of the first position is 1, not 0.

**Some examples:**

- For the `sequence` "ACGTGGGGACTAGGGG" and the `motif` "GGGG" the result should be [5, 13]. 
- For the `sequence` "ACCGTACCAAGGGACC" and the `motif` "AAT"  the result should be []
- For the `sequence` "GGG" and the motif "GG" the result should be [1, 2]

**Note**: You can take a look to my others bio-info kata [here](http://www.codewars.com/users/nbeck/authored)

def DnaBases : List Char := ['A', 'C', 'G', 'T']

def isValidDnaChar (c : Char) : Bool :=
  match DnaBases.find? (· == c) with
  | some _ => true 
  | none => false

def isValidDnaString (s : String) : Bool :=
  match s.data.find? (fun c => !isValidDnaChar c) with
  | some _ => false
  | none => true 

def motif_locator (sequence motif : String) : List Nat :=
sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded