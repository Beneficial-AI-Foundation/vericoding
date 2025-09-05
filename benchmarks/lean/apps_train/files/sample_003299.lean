Implement a function/class, which should return an integer if the input string is in one of the formats specified below, or `null/nil/None` otherwise.

Format:
* Optional `-` or `+`
* Base prefix `0b` (binary), `0x` (hexadecimal), `0o` (octal), or in case of no prefix decimal.
* Digits depending on base

Any extra character (including whitespace) makes the input invalid, in which case you should return `null/nil/None`.

Digits are case insensitive, but base prefix must be lower case.

See the test cases for examples.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded