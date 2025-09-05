Write a program that will take a string of digits and give you all the possible consecutive slices of length `n` in that string.

Raise an error if `n` is larger than the length of the string.

## Examples

For example, the string `"01234"` has the following 2-digit slices:
```
[0, 1], [1, 2], [2, 3], [3, 4]
```

The same string has the following 4-digit slices:
```
[0, 1, 2, 3], [1, 2, 3, 4]
```

def Digit := Nat
def NumStr := List Digit

instance : OfNat Digit n where
  ofNat := n

instance : LE Digit where
  le := Nat.le

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
