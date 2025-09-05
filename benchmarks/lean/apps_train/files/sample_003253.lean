A [Word Square](https://en.wikipedia.org/wiki/Word_square) is a set of words written out in a square grid, such that the same words can be read both horizontally and vertically. The number of words, equal to the number of letters in each word, is known as the *order* of the square.

For example, this is an *order* `5` square found in the ruins of Herculaneum:

![](https://i.gyazo.com/e226262e3ada421d4323369fb6cf66a6.jpg)

Given a string of various uppercase `letters`, check whether a *Word Square* can be formed from it. 

Note that you should use each letter from `letters` the exact number of times it occurs in the string. If a *Word Square* can be formed, return `true`, otherwise return `false`.

__Example__

  * For `letters = "SATORAREPOTENETOPERAROTAS"`, the output should be
  `WordSquare(letters) = true`.
    It is possible to form a *word square* in the example above.

  * For `letters = "AAAAEEEENOOOOPPRRRRSSTTTT"`, (which is sorted form of `"SATORAREPOTENETOPERAROTAS"`), the output should also be
  `WordSquare(letters) = true`.

  * For `letters = "NOTSQUARE"`, the output should be
  `WordSquare(letters) = false`.

__Input/Output__

* [input] string letters

  A string of uppercase English letters.

  Constraints: `3 ≤ letters.length ≤ 100`.

* [output] boolean

  `true`, if a Word Square can be formed;

  `false`, if a Word Square cannot be formed.

def word_square (s : String) : Bool := sorry

theorem non_square_length_strings_are_false {s : String} 
  (h : ∃ n : Nat, n * n ≠ s.length) : 
  word_square s = false := sorry

def countChar (c : Char) (s : List Char) : Nat :=
  (s.filter (fun x => x = c)).length

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
