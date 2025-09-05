In this Kata, you will be given a string with brackets and an index of an opening bracket and your task will be to return the index of the matching closing bracket.  Both the input and returned index are 0-based **except in Fortran where it is 1-based**. An opening brace will always have a closing brace. Return `-1` if there is no answer (in Haskell, return `Nothing`; in Fortran, return `0`; in Go, return an error)

### Examples

```python
solve("((1)23(45))(aB)", 0) = 10 -- the opening brace at index 0 matches the closing brace at index 10
solve("((1)23(45))(aB)", 1) = 3 
solve("((1)23(45))(aB)", 2) = -1 -- there is no opening bracket at index 2, so return -1
solve("((1)23(45))(aB)", 6) = 9
solve("((1)23(45))(aB)", 11) = 14
solve("((>)|?(*'))(yZ)", 11) = 14
```

Input will consist of letters, numbers and special characters, but no spaces. The only brackets will be `(` and `)`. 

More examples in the test cases. 

Good luck!

~~~if:fortran
*NOTE: In Fortran, you may assume that the input string will not contain any leading/trailing whitespace.*
~~~

def solve (s : String) (idx : Nat) : Int := sorry

def has_matching_parens (s : String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded