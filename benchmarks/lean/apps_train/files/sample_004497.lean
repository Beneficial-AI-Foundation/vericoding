Similar to the [previous kata](https://www.codewars.com/kata/string-subpattern-recognition-ii/), but this time you need to operate with shuffled strings to identify if they are composed repeating a subpattern

Since there is no deterministic way to tell which pattern was really the original one among all the possible permutations of a fitting subpattern, return a subpattern with sorted characters, otherwise return the base string with sorted characters (you might consider this case as an edge case, with the subpattern being repeated only once and thus equalling the original input string).

For example:

```python
has_subpattern("a") == "a"; #no repeated pattern, just one character
has_subpattern("aaaa") == "a" #just one character repeated
has_subpattern("abcd") == "abcd" #base pattern equals the string itself, no repetitions
has_subpattern("babababababababa") == "ab" #remember to return the base string sorted"
has_subpattern("bbabbaaabbaaaabb") == "ab" #same as above, just shuffled
```

If you liked it, go for either the [previous kata](https://www.codewars.com/kata/string-subpattern-recognition-ii/) or the [next kata](https://www.codewars.com/kata/string-subpattern-recognition-iv/) of the series!

def String.count (s : String) (c : Char) : Nat := sorry
def String.toCharArray (s : String) : Array Char := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
