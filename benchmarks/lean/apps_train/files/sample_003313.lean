Find the longest substring within a string that contains at most 2 unique characters.

```
substring("a") => "a"
substring("aaa") => "aaa"
substring("abacd") => "aba"
substring("abacddcd") => "cddcd"
substring("cefageaacceaccacca") => "accacca"
```

This function will take alphanumeric characters as input.

In cases where there could be more than one correct answer, the first string occurrence should be used. For example, substring('abc') should return 'ab' instead of 'bc'.

Although there are O(N^2) solutions to this problem, you should try to solve this problem in O(N) time. Tests may pass for O(N^2) solutions but, this is not guaranteed.

This question is much harder than some of the other substring questions. It's easy to think that you have a solution and then get hung up on the implementation.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
