##Task:
You have to write a function `add` which takes two binary numbers as strings and returns their sum as a string.

##Note:
* You are `not allowed to convert binary to decimal & vice versa`.
* The sum should contain `No leading zeroes`.

##Examples:
```
add('111','10'); => '1001'
add('1101','101'); => '10010'
add('1101','10111') => '100100'
```

def add (a b : String) : String := sorry

def binary_to_int (s : String) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded