/-
The vowel substrings in the word `codewarriors` are `o,e,a,io`. The longest of these has a length of 2. Given a lowercase string that has alphabetic characters only (both vowels and consonants) and no spaces, return the length of the longest vowel substring.
Vowels are any of `aeiou`. 

```if:csharp
Documentation:
Kata.Solve Method (String)

Returns the length of the greatest continuous vowel substring in a string.

Syntax

public
static
int Solve(
string str
    )

Parameters

str

Type: System.String
The string to be processed.

Return Value

Type: System.Int32
  The length of the greatest continuous vowel substring in str, or 0 if str contains no vowels.

Exceptions

Exception
Condition

ArgumentNullException
str is null.

```

Good luck!

If you like substring Katas, please try:

[Non-even substrings](https://www.codewars.com/kata/59da47fa27ee00a8b90000b4)

[Vowel-consonant lexicon](https://www.codewars.com/kata/59cf8bed1a68b75ffb000026)
-/

def vowel (c : Char) : Bool :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def solve (s : String) : Nat :=
sorry

theorem solve_all_vowels (s : String) 
  (h₁ : s.length > 0)
  (h₂ : ∀ c ∈ s.data, vowel c = true) :
  solve s = s.length :=
sorry

theorem solve_interspersed
  (vowels : List String)
  (consonants : List String)
  (h₁ : vowels.length > 0) 
  (h₂ : ∀ s ∈ vowels, s.length > 0)
  (h₃ : ∀ s ∈ vowels, ∀ c ∈ s.data, vowel c = true)
  (h₄ : ∀ s ∈ consonants, ∀ c ∈ s.data, vowel c = false) :
  let combined := List.zip vowels consonants
  let s := String.join (combined.map (fun p => p.1 ++ p.2))
  solve s ≥ (List.foldl (fun acc x => max acc x.length) 0 vowels) :=
sorry

-- Apps difficulty: introductory
-- Assurance level: guarded