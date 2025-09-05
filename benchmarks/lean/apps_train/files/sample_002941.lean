You like the way the Python `+` operator easily handles adding different numeric types, but you need a tool to do that kind of addition without killing your program with a `TypeError` exception whenever you accidentally try adding incompatible types like strings and lists to numbers.

You decide to write a function `my_add()` that takes two arguments. If the arguments can be added together it returns the sum. If adding the arguments together would raise an error the function should return `None` instead.

For example, `my_add(1, 3.414)` would return `4.414`, but `my_add(42, " is the answer.")` would return `None`.

Hint: using a `try` / `except` statement may simplify this kata.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
