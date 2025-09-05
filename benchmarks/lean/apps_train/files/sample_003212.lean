The look and say sequence is a sequence in which each number is the result of a "look and say" operation on the previous element.

Considering for example the classical version startin with `"1"`: `["1", "11", "21, "1211", "111221", ...]`. You can see that the second element describes the first as `"1(times number)1"`, the third is `"2(times number)1"` describing the second, the fourth is `"1(times number)2(and)1(times number)1"` and so on.

Your goal is to create a function which takes a starting string (not necessarily the classical `"1"`, much less a single character start) and return the nth element of the series.

## Examples

```python
look_and_say_sequence("1", 1)   == "1"
look_and_say_sequence("1", 3)   == "21"
look_and_say_sequence("1", 5)   == "111221"
look_and_say_sequence("22", 10) == "22"
look_and_say_sequence("14", 2)  == "1114"
```
Trivia: `"22"` is the only element that can keep the series constant.

def isDigit (c : Char) : Bool := sorry

def isNonZeroDigit (c : Char) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
