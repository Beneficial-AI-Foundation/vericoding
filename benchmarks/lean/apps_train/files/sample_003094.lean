Given a string, remove any characters that are unique from the string.

Example: 

input: "abccdefee"

output: "cceee"

def countChar (s : String) (c : Char) : Nat :=
  s.toList.filter (· = c) |>.length

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
