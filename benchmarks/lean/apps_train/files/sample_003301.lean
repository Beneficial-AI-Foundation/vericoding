Define a method that accepts 2 strings as parameters. The method returns the first string sorted by the second.

```python
sort_string("foos", "of")       == "oofs"
sort_string("string", "gnirts") == "gnirts"
sort_string("banana", "abn")    == "aaabnn"
```

To elaborate, the second string defines the ordering. It is possible that in the second string characters repeat, so you should remove repeating characters, leaving only the first occurrence.

Any character in the first string that does not appear in the second string should be sorted to the end of the result in original order.

def sort_string (s : String) (ordering : String) : String :=
  sorry

/-- Helper function to count occurrences of a character in a string -/

def String.countChar (s : String) (c : Char) : Nat :=
  s.data.filter (· = c) |>.length

/-- Helper function to find first index of character in string -/

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded