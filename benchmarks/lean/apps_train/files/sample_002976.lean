In this kata you need to build a function to return either `true/True` or `false/False` if a string can be seen as the repetition of a simpler/shorter subpattern or not.

For example:

```cpp,java
hasSubpattern("a") == false; //no repeated pattern
hasSubpattern("aaaa") == true; //created repeating "a"
hasSubpattern("abcd") == false; //no repeated pattern
hasSubpattern("abababab") == true; //created repeating "ab"
hasSubpattern("ababababa") == false; //cannot be entirely reproduced repeating a pattern
```
```python
has_subpattern("a") == False #no repeated pattern
has_subpattern("aaaa") == True #created repeating "a"
has_subpattern("abcd") == False #no repeated pattern
has_subpattern("abababab") == True #created repeating "ab"
has_subpattern("ababababa") == False #cannot be entirely reproduced repeating a pattern
```
Strings will never be empty and can be composed of any character (just consider upper- and lowercase letters as different entities) and can be pretty long (keep an eye on performances!).

If you liked it, go for the [next kata](https://www.codewars.com/kata/string-subpattern-recognition-ii/) of the series!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
