Given a string ``string`` that contains only letters, you have to find out the number of **unique** strings (including ``string`` itself) that can be produced by re-arranging the letters of the ``string``.  Strings are case **insensitive**.

HINT: Generating all the unique strings and calling length on that isn't a great solution for this problem. It can be done a lot faster...

## Examples

```python
uniqcount("AB") = 2      # "AB", "BA"
uniqcount("ABC") = 6     # "ABC", "ACB", "BAC", "BCA", "CAB", "CBA"
uniqcount("ABA") = 3     # "AAB", "ABA", "BAA"
uniqcount("ABBb") = 4    # "ABBB", "BABB", "BBAB", "BBBA"
uniqcount("AbcD") = 24   # "ABCD", etc.
```

def factorial : Nat → Nat
  | 0 => 1 
  | n + 1 => (n + 1) * factorial n

def List.prod : List Nat → Nat
  | [] => 1
  | x :: xs => x * prod xs

def isAscii (s : String) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
