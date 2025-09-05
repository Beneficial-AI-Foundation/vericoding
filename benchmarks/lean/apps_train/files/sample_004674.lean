Design a data structure that supports the following two operations:

* `addWord` (or `add_word`) which adds a word,
* `search` which searches a literal word or a regular expression string containing lowercase letters `"a-z"` or `"."` where `"."` can represent any letter

You may assume that all given words contain only lowercase letters.

## Examples
```python
add_word("bad")
add_word("dad")
add_word("mad")

search("pad") == False
search("bad") == True
search(".ad") == True
search("b..") == True
```

**Note:** the data structure will be initialized multiple times during the tests!

def WordDictionary.addWord (wd : WordDictionary) (word : String) : WordDictionary :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
