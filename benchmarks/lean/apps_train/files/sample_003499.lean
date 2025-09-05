Your task is to define a function that understands basic mathematical expressions and solves them.
For example:

```python
calculate("1 + 1")        # => 2
calculate("18 + 4*6")     # => 42
calculate("245 - 826")    # => -581
calculate("09 + 000482")  # => 491
calculate("8 / 4 + 6")    # => 8
calculate("5 + 1 / 5")    # => 5.2
calculate("1+2+3")        # => 6
calculate("9 /3 + 12/ 6") # => 5
```
Notes:

- Input string will contain numbers (may be integers and floats) and arithmetic operations.
- Input string may contain spaces, and all space characters should be ignored.
- Operations that will be used: addition (+), subtraction (-), multiplication (*), and division (/)
- Operations must be done in the order of operations: First multiplication and division, then addition and subtraction.
- In this kata, input expression will not have negative numbers. (ex: "-4 + 5")
- If output is an integer, return as integer. Else return as float.
- If input string is empty, contains letters, has a wrong syntax, contains division by zero or is not a string, return False.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded