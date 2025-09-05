While most devs know about [big/little-endianness](https://en.wikipedia.org/wiki/Endianness), only a selected few know the secret of real hard core coolness with mid-endians.

Your task is to take a number and return it in its mid-endian format, putting the most significant couple of bytes in the middle and all the others around it, alternating left and right.

For example, consider the number `9999999`, whose hexadecimal representation would be `98967F` in big endian (the classic you get converting); it becomes `7F9698` in little-endian and `96987F` in mid-endian.

Write a function to do that given a positive integer (in base 10) and remembering that you need to pad with `0`s when you get a single hex digit!

def mid_endian (n : Nat) : String := sorry

def natToHexString (n : Nat) : String := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded