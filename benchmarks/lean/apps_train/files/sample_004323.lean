Consider the string `"adfa"` and the following rules: 
```Pearl
a) each character MUST be changed either to the one before or the one after in alphabet. 
b) "a" can only be changed to "b" and "z" to "y". 
```
From our string, we get:
```Pearl
"adfa" -> ["begb","beeb","bcgb","bceb"]
Another example: "bd" -> ["ae","ac","ce","cc"]
--We see that in each example, one of the possibilities is a palindrome.
```
I was working on the code for this but I couldn't quite figure it out. So far I have:

```python
def solve(st):
    return [all(ord(x) - ord(y) in ["FIX"] for x, y in zip(st, st[::-1]))][0]
```
I'm not sure what three numbers go into the array labelled `["FIX"]`. This is the only thing missing. 

You will be given a lowercase string and your task is to return `True` if at least one of the possiblities is a palindrome or `False` otherwise. You can use your own code or fix mine. 

More examples in test cases. Good luck!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded