/-
In this kata, you need to make a (simplified) LZ78 encoder and decoder.
[LZ78](https://en.wikipedia.org/wiki/LZ77_and_LZ78#LZ78) is a dictionary-based compression method created in 1978. You will find a  detailed explanation about how it works below.

The input parameter will always be a non-empty string of upper case alphabetical characters. The maximum decoded string length is 1000 characters.

# Instructions

*If anyone has any ideas on how to make the instructions shorter / clearer, that would be greatly appreciated.*

If the below explanation is too confusing, just leave a comment and I'll be happy to help.

---

The input is looked at letter by letter.
Each letter wants to be matched with the longest dictionary substring at that current time.

The output is made up of tokens.
Each token is in the format ``
where `index` is the index of the longest dictionary value that matches the current substring
and `letter` is the current letter being looked at.

Here is how the string `'ABAABABAABAB'` is encoded:

* First, a dictionary is initialised with the 0th item pointing to an empty string:

```md
Dictionary      Input             Output
0  |  ''        ABAABABAABAB
```

* The first letter is `A`. As it doesn't appear in the dictionary, we add `A` to the next avaliable index.
The token `<0, A>` is added to the output:

```md
Dictionary      Input             Output

0  |  ''        ABAABABAABAB      <0, A>
1  |  A         ^
```

* The second letter is `B`. It doesn't appear in the dictionary, so we add `B` to the next avaliable index.
The token `<0, B>` is added to the output:

```md
Dictionary      Input             Output

0  |  ''        ABAABABAABAB      <0, A> <0, B>
1  |  A          ^
2  |  B
```

* The third letter is `A` again: it already appears in the dictionary at position `1`. We add the next letter which is also `A`. `AA` doesn't appear in the dictionary, so we add it to the next avaliable index.
The token `<1, A>` is added to the output:

```md
Dictionary      Input             Output

0  |  ''        ABAABABAABAB      <0, A> <0, B> <1, A>
1  |  A           ^^
2  |  B
3  |  AA
```

* The next letter is `B` again: it already appears in the dictionary at position `2`. We add the next letter which is `A`. `BA` doesn't appear in the dictionary, so we add it to the next avaliable index.
The token `<2, A>` is added to the output:

```md
Dictionary      Input             Output

0  |  ''        ABAABABAABAB      <0, A> <0, B> <1, A> <2, A>
1  |  A             ^^
2  |  B
3  |  AA
4  |  BA
```

* The next letter is `B`: it already appears in the dictionary and at position `2`. We add the next letter which is `A`. `BA` already appears in the dictionary at position `4`. We add the next letter which is `A`. `BAA` doesn't appear in the dictionary, so we add it to the next avaliable index.
The token `<4, A>` is added to the output:

```md
Dictionary      Input             Output

0  |  ''        ABAABABAABAB      <0, A> <0, B> <1, A> <2, A> <4, A>
1  |  A               ^^^
2  |  B
3  |  AA
4  |  BA
5  |  BAA
```

* The next letter is `B`. It already appears in the dictionary at position `2`. We add the next letter which is `A`. `BA` already appears in the dictionary at position `4`. We add the next letter which is `B`. `BAB` doesn't appear in the dictionary, so we add it to the next avaliable index.
The token `<4, B>` is added to the output:

```md
Dictionary      Input             Output

0  |  ''        ABAABABAABAB      <0, A> <0, B> <1, A> <2, A> <4, A> <4, B>
1  |  A                  ^^^
2  |  B
3  |  AA
4  |  BA
5  |  BAA
6  |  BAB
```

* We have now reached the end of the string. We have the output tokens: `<0, A> <0, B> <1, A> <2, A> <4, A> <4, B>`.
Now we just return the tokens without the formatting: `'0A0B1A2A4A4B'`

**Note:**

If the string ends with a match in the dictionary, the last token should only contain the index of the dictionary. For example, `'ABAABABAABABAA'` (same as the example but with `'AA'` at the end) should return `'0A0B1A2A4A4B3'` (note the final `3`).

To decode, it just works the other way around.

# Examples

Some more examples:
```
Decoded                               Encoded

ABBCBCABABCAABCAABBCAA                0A0B2C3A2A4A6B6
AAAAAAAAAAAAAAA                       0A1A2A3A4A
ABCABCABCABCABCABC                    0A0B0C1B3A2C4C7A6
ABCDDEFGABCDEDBBDEAAEDAEDCDABC        0A0B0C0D4E0F0G1B3D0E4B2D10A1E4A10D9A2C
```

Good luck :)
-/

def encoder (s : String) : String := sorry
def decoder (s : String) : String := sorry

-- Helper function to check if character is uppercase

def isUpper (c : Char) : Bool := sorry

-- Helper function to check if character is digit

def isDigit (c : Char) : Bool := sorry

-- Helper function to check if string starts with 0 and uppercase letter

-- <vc-helpers>
-- </vc-helpers>

def startsWithZeroUpper (s : String) : Bool := sorry

theorem encoder_output_format (s : String) (h : s ≠ "") : 
  (∀ c, c ∈ s.toList → isDigit c ∨ isUpper c) ∧ 
  startsWithZeroUpper (encoder s) := sorry

theorem encoder_length_bounds (s : String) (h : s ≠ "") :
  String.length (encoder s) ≤ 3 * String.length s ∧
  String.length (encoder s) ≥ String.length s / 2 := sorry

theorem encoder_decoder_inverse (s : String) (h : s ≠ "") :
  decoder (encoder s) = s := sorry

-- Apps difficulty: introductory
-- Assurance level: unguarded