# Task
 Given a string `s`, find out if its characters can be rearranged to form a palindrome.

# Example

 For `s = "aabb"`, the output should be `true`.

 We can rearrange `"aabb"` to make `"abba"`, which is a palindrome.

# Input/Output

 - `[input]` string `s`

    A string consisting of lowercase English letters.

    Constraints:

    `4 ≤ inputString.length ≤ 50.`

 - `[output]` a boolean value

    `true` if the characters of the inputString can be rearranged to form a palindrome, `false` otherwise.

def palindrome_rearranging (s : String) : Bool :=
  sorry

def String.reverse (s : String) : String :=
  sorry

def String.repeating (c : Char) (n : Nat) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded