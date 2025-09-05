# Task

Write a function `deNico`/`de_nico()` that accepts two parameters:
- `key`/`$key` - string consists of unique letters and digits
- `message`/`$message` - string with encoded message 

and decodes the `message` using the `key`.  

First create a numeric key basing on the provided `key` by assigning each letter position in which it is located after setting the letters from `key` in an alphabetical order.

For example, for the key `crazy` we will get `23154` because of `acryz` (sorted letters from the key).  
Let's decode  `cseerntiofarmit on  ` using our `crazy` key.

```
1 2 3 4 5
---------
c s e e r
n t i o f
a r m i t
  o n   
```

After using the key:
```
2 3 1 5 4
---------
s e c r e
t i n f o
r m a t i
o n
```

# Notes 

- The `message` is never shorter than the `key`.
- Don't forget to remove trailing whitespace after decoding the message

# Examples

Check the test cases for more examples.

# Related Kata

[Basic Nico - encode](https://www.codewars.com/kata/5968bb83c307f0bb86000015)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
