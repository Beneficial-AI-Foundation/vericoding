This is a follow-up from my previous Kata which can be found here: http://www.codewars.com/kata/5476f4ca03810c0fc0000098

This time, for any given linear sequence, calculate the function [f(x)] and return it as a function in Javascript or Lambda/Block in Ruby.

For example:

```python
get_function([0, 1, 2, 3, 4])(5) => 5
get_function([0, 3, 6, 9, 12])(10) => 30
get_function([1, 4, 7, 10, 13])(20) => 61
```

Assumptions for this kata are:
```
The sequence argument will always contain 5 values equal to f(0) - f(4).
The function will always be in the format "nx +/- m", 'x +/- m', 'nx', 'x' or 'm'
If a non-linear sequence simply return 'Non-linear sequence' for javascript, ruby, and python. For C#, throw an ArgumentException.
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
