## Task

You will receive a string consisting of lowercase letters, uppercase letters and digits as input. Your task is to return this string as blocks separated by dashes (`"-"`). The elements of a block should be sorted with respect to the hierarchy listed below, and each block cannot contain multiple instances of the same character. Elements should be put into the first suitable block.

The hierarchy is:
1. lowercase letters (`a - z`), in alphabetical order
2. uppercase letters (`A - Z`), in alphabetical order
3. digits (`0 - 9`), in ascending order

## Examples

* `"21AxBz" -> "xzAB12"` - since input does not contain repeating characters, you only need 1 block
* `"abacad" -> "abcd-a-a"` - character "a" repeats 3 times, thus 3 blocks are needed
* `"" -> ""` - an empty input should result in an empty output
* `"hbh420sUUW222IWOxndjn93cdop69NICEep832" -> "bcdehjnopsxCEINOUW0234689-dhnpIUW239-2-2-2"` - a more sophisticated example

Good luck!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
