Challenge:
Given two null-terminated strings in the arguments "string" and "prefix", determine if "string" starts with the "prefix" string. Return 1 (or any other "truthy" value) if true, 0 if false.

Example:
```
startsWith("hello world!", "hello"); // should return 1.
startsWith("hello world!", "HELLO"); // should return 0.
startsWith("nowai", "nowaisir"); // should return 0.
```

Addendum:
For this problem, an empty "prefix" string should always return 1 (true) for any value of "string".

If the length of the "prefix" string is greater than the length of the "string", return 0.

The check should be case-sensitive, i.e. startsWith("hello", "HE") should return 0, whereas startsWith("hello", "he") should return 1.

The length of the "string" as well as the "prefix" can be defined by the formula: 0 <= length < +Infinity

No characters should be ignored and/or omitted during the test, e.g. whitespace characters should not be ignored.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
