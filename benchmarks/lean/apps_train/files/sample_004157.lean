# Right in the Center

_This is inspired by one of Nick Parlante's exercises on the [CodingBat](https://codingbat.com/java) online code practice tool._

Given a sequence of characters, does `"abc"` appear in the CENTER of the sequence?

The sequence of characters could contain more than one `"abc"`.

To define CENTER, the number of characters in the sequence to the left and right of the "abc" (which is in the middle) must differ by at most one.

If it is in the CENTER, return `True`. Otherwise, return `False`.

Write a function as the solution for this problem. This kata looks simple, but it might not be easy.

## Example

    is_in_middle("AAabcBB")  ->  True
    is_in_middle("AabcBB")   ->  True
    is_in_middle("AabcBBB")  ->  False

def is_in_middle (s : String) : Bool := sorry

theorem empty_or_short_string (s : String) :
  s.length ≤ 3 → is_in_middle s = false := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
