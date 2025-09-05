# Task

Christmas is coming. In the [previous kata](https://www.codewars.com/kata/5a405ba4e1ce0e1d7800012e), we build a custom Christmas tree with the specified characters and the specified height.

Now, we are interested in the center of the Christmas tree. 

Please imagine that we build a Christmas tree with `chars = "abc" and n = Infinity`, we got:
```
          a
         b c
        a b c
       a b c a
      b c a b c
     a b c a b c
    a b c a b c a
   b c a b c a b c
  a b c a b c a b a
 b c a b c a b a b c
a b c a b a b c a b c
. . . . . . . . . . .
. . . . . . . . . . .
. . . . . . . . . . .
. . . . . . . . . . .
          |
          |
          .
          .
```
If we keep only the center part of leaves, we will got:
```
          a

          b  

          a    

          a        

          b        

          a          
          .

          .

          .
```
As you can see, it's a infinite string, but it has a repeat substring "aba"(spaces will be removed). If we join them together, it looks like:`"abaabaabaabaaba......"`.

So, your task is to find the repeat substring of the center part of leaves.

# Inputs:

- `chars`: the specified characters. In this kata, they always be lowercase letters.

# Output:

- The repeat substring that satisfy the above conditions.

Still not understand the task? Look at the following example ;-)

# Examples

For `chars = "abc"`,the output should be `"aba"`
```
center leaves sequence: "abaabaabaabaabaaba....."
```
For `chars = "abab"`,the output should be `a`
```
center leaves sequence: "aaaaaaaaaa....."
```
For `chars = "abcde"`,the output should be `aecea`
```
center leaves sequence: "aeceaaeceaaecea....."
```
For `chars = "aaaaaaaaaaaaaa"`,the output should be `a`
```
center leaves sequence: "aaaaaaaaaaaaaa....."
```
For `chars = "abaabaaab"`,the output should be `aba`
```
center leaves sequence: "abaabaabaaba....."
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
