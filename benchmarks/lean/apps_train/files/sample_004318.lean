# Do names have colors?

*Now they do.*

Make a function that takes in a name (Any string two chars or longer really, but the name is the idea) and use the ascii values of it's substrings to produce the hex value of its color! Here is how it's going to work:

* The first two hexadecimal digits are the *SUM* of the value of characters (modulo 256).
* The second two are the *PRODUCT* of all the characters (again, modulo 256, which is one more than `FF` in hexadecimal).
* The last two are the *ABSOLUTE VALUE of the DIFFERENCE* between the first letter, and the sum of every other letter. (I think you get the idea with the modulo thing).

For example `"Jack"` returns `"79CAE5"`, which is... **baby blue!**
```
"Jack"  #  "J" = 74, "a" = 97, "c" = 99, "k" = 107

74 + 97 + 99 + 107 = 377                   -->  mod 256 = 121  -->  hex: 79
74 * 97 * 99 * 107 = 76036554              -->  mod 256 = 202  -->  hex: CA
74 - (97 + 99 + 107) = -229  --> abs: 229  -->  mod 256 = 229  -->  hex: E5
```

NOTE: The function should return `None/nil` when the input is less than two chars.

def string_color (s : String) : Option String := sorry

theorem string_color_short_strings {s : String} (h : s.length ≤ 1) : 
  string_color s = none := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
