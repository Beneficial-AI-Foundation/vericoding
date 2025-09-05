# Task

John has an important number, and he doesn't want others to see it.

He decided to encrypt the number, using the following steps:
```
His number is always a non strict increasing sequence
ie. "123"

He converted each digit into English words.
ie. "123"--> "ONETWOTHREE"

And then, rearrange the letters randomly.
ie. "ONETWOTHREE" --> "TTONWOHREEE"
```

John felt that his number were safe in doing so. In fact, such encryption can be easily decrypted :(

Given the encrypted string `s`, your task is to decrypt it, return the original number in string format.

Note, You can assume that the input string `s` is always valid; It contains only uppercase Letters; The decrypted numbers are arranged in ascending order; The leading zeros are allowed.

# Example

For `s = "ONE"`, the output should be `1`.

For `s = "EON"`, the output should be `1` too.

For `s = "ONETWO"`, the output should be `12`.

For `s = "OONETW"`, the output should be `12` too.

For `s = "ONETWOTHREE"`, the output should be `123`.

For `s = "TTONWOHREEE"`, the output should be `123` too.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
