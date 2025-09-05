### Description:

 Remove all exclamation marks from sentence except at the end.

### Examples

```
remove("Hi!") == "Hi!"
remove("Hi!!!") == "Hi!!!"
remove("!Hi") == "Hi"
remove("!Hi!") == "Hi!"
remove("Hi! Hi!") == "Hi Hi!"
remove("Hi") == "Hi"
```

def remove (s : String) : String := sorry

def countChar (s : String) (c : Char) : Nat :=
  s.data.filter (· = c) |>.length

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
