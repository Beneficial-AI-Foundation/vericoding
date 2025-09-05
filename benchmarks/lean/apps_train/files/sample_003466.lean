# Task

Write a function that accepts `msg` string and returns local tops of string from the highest to the lowest.  
The string's tops are from displaying the string in the below way:

```

                                         7891012
                             TUWvXY      6     3
                   ABCDE     S    Z      5
           lmno    z   F     R    1      4
     abc   k  p    v   G     Q    2      3
.34..9 d...j  q....x   H.....P    3......2
125678 efghi  rstuwy   IJKLMNO    45678901

```
The next top is always 1 character higher than the previous one. 
For the above example, the solution for the `123456789abcdefghijklmnopqrstuwyxvzABCDEFGHIJKLMNOPQRSTUWvXYZ123456789012345678910123` input string is `7891012TUWvXYABCDElmnoabc34`. 

- When the `msg` string is empty, return an empty string.
- The input strings may be very long. Make sure your solution has good performance.
- The (.)dots on the sample dispaly of string are only there to help you to understand the pattern  

Check the test cases for more samples.

# Series

- [String tops](https://www.codewars.com/kata/59b7571bbf10a48c75000070)
- [Square string tops](https://www.codewars.com/kata/5aa3e2b0373c2e4b420009af)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
