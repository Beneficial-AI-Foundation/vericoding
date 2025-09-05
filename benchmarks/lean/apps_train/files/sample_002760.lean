Given a string, return a new string that has transformed based on the input:

* Change case of every character, ie. lower case to upper case, upper case to lower case.
* Reverse the order of words from the input.

**Note:** You will have to handle multiple spaces, and leading/trailing spaces.

For example:

```
"Example Input" ==> "iNPUT eXAMPLE"
```

You may assume the input only contain English alphabet and spaces.

def string_transformer (s : String) : String := sorry

def countSpaces (s : String) : Nat :=
  s.toList.foldl (fun count c => if c = ' ' then count + 1 else count) 0

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded