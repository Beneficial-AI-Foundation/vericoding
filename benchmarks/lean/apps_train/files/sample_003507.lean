Much cooler than your run-of-the-mill Fibonacci numbers, the Triple Shiftian are so defined: `T[n] = 4 * T[n-1] - 5 * T[n-2] + 3 * T[n-3]`.

You are asked to create a function which accept a base with the first 3 numbers and then returns the nth element.
```python
triple_shiftian([1,1,1],25) == 1219856746
triple_shiftian([1,2,3],25) == 2052198929
triple_shiftian([6,7,2],25) == -2575238999
triple_shiftian([3,2,1],35) == 23471258855679
triple_shiftian([1,9,2],2) ==  2
```
*Note: this is meant to be an interview quiz, so the description is scarce in detail on purpose*

Special thanks to the [first person I met in person here in London just because of CW](http://www.codewars.com/users/webtechalex) and that assisted me during the creation of this kata ;)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded