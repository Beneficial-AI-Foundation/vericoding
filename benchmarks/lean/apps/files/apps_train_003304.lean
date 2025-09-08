/-
Write a method that takes a string as an argument and groups the number of time each character appears in the string as a hash sorted by the highest number of occurrences.

The characters should be sorted alphabetically e.g:

```python
get_char_count("cba") == {1: ["a", "b", "c"]}
```

You should ignore spaces, special characters and count uppercase letters as lowercase ones.

For example: 
```python
get_char_count("Mississippi")           ==  {4: ["i", "s"], 2: ["p"], 1: ["m"]}
get_char_count("Hello. Hello? HELLO!")  ==  {6: ["l"], 3: ["e", "h", "o"]}
get_char_count("aaa...bb...c!")         ==  {3: ["a"], 2: ["b"], 1: ["c"]}
get_char_count("abc123")                ==  {1: ["1", "2", "3", "a", "b", "c"]}
get_char_count("aaabbbccc")             ==  {3: ["a", "b", "c"]}
```
-/

-- <vc-helpers>
-- </vc-helpers>

def get_char_count (s : String) : List (Nat × List Char) :=
  sorry

theorem get_char_count_empty :
  get_char_count "" = [] := 
  sorry

theorem get_char_count_single (c : Char) :
  get_char_count (String.singleton c) = [(1, [c])] :=
  sorry

theorem get_char_count_duplicates :
  get_char_count "aaa" = [(3, ['a'])] :=
  sorry

theorem get_char_count_distinct :
  let res := get_char_count "abc"
  ∃ l, (1, l) ∈ res ∧ l = ['a', 'b', 'c'] :=
  sorry

theorem get_char_count_mixed :
  get_char_count "mississippi" = [(4, ['i', 's']), (2, ['p']), (1, ['m'])] :=
  sorry

-- Apps difficulty: introductory
-- Assurance level: guarded