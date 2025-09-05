In this Kata, you will be given a lower case string and your task will be to remove `k` characters from that string using the following rule:
```Python
- first remove all letter 'a', followed by letter 'b', then 'c', etc...
- remove the leftmost character first.
```

```Python
For example: 
solve('abracadabra', 1) = 'bracadabra' # remove the leftmost 'a'.
solve('abracadabra', 2) = 'brcadabra'  # remove 2 'a' from the left.
solve('abracadabra', 6) = 'rcdbr'      # remove 5 'a', remove 1 'b' 
solve('abracadabra', 8) = 'rdr'
solve('abracadabra',50) = ''
```

More examples in the test cases. Good luck!

Please also try: 

[Simple time difference](https://www.codewars.com/kata/5b76a34ff71e5de9db0000f2)

[Simple remove duplicates](https://www.codewars.com/kata/5ba38ba180824a86850000f7)

def solve (text : String) (k : Nat) : String := sorry

def get_char_indices (s : String) (c : Char) : List Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded