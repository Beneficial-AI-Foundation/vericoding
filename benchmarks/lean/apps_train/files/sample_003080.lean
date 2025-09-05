# Task
A newspaper is published in Walrusland. Its heading is `s1` , it consists of lowercase Latin letters. 

Fangy the little walrus wants to buy several such newspapers, cut out their headings, glue them one to another in order to get one big string. 

After that walrus erase several letters from this string in order to get a new word `s2`. 

It is considered that when Fangy erases some letter, there's no whitespace formed instead of the letter. That is, the string remains unbroken and it still only consists of lowercase Latin letters.

For example, the heading is `"abc"`. If we take two such headings and glue them one to the other one, we get `"abcabc"`. If we erase the 1st letter("a") and 5th letter("b"), we get a word `"bcac"`.

Given two string `s1` and `s2`, return the least number of newspaper headings `s1`, which Fangy will need to receive the word `s2`. If it is impossible to get the word `s2` in the above-described manner, return `-1`.

# Example

For `s1="abc", s2="bcac"`, the output should be `2`.

```
"abcabc" --> "bcac"
 x   x
```

For `s1="abc", s2="xyz"`, the output should be `-1`.

It's impossible to get the word `s2`.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded