Your job is to write a function that takes a string and a maximum number of characters per line and then inserts line breaks as necessary so that no line in the resulting string is longer than the specified limit.

If possible, line breaks should not split words. However, if a single word is longer than the limit, it obviously has to be split. In this case, the line break should be placed after the first part of the word (see examples below).

Really long words may need to be split multiple times.

#Input

A word consists of one or more letters.

Input text will be the empty string or a string consisting of one or more words separated by single spaces. It will not contain any punctiation or other special characters.

The limit will always be an integer greater or equal to one.

#Examples

**Note:** Line breaks in the results have been replaced with two dashes to improve readability.

1. ("test", 7) -> "test"
2. ("hello world", 7) -> "hello--world"
3. ("a lot of words for a single line", 10) -> "a lot of--words for--a single--line"
4. ("this is a test", 4) -> "this--is a--test"
5. ("a longword", 6) -> "a long--word"
6. ("areallylongword", 6) -> "areall--ylongw--ord"

**Note:** Sometimes spaces are hard to see in the test results window.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded