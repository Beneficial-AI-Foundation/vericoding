Consider the word `"abode"`. We can see that the letter `a` is in position `1` and `b` is in position `2`. In the alphabet, `a` and `b` are also in positions `1` and `2`. Notice also that `d` and `e` in `abode` occupy the positions they would occupy in the alphabet, which are positions `4` and `5`. 

Given an array of words, return an array of the number of letters that occupy their positions in the alphabet for each word. For example,
```
solve(["abode","ABc","xyzD"]) = [4, 3, 1]
```
See test cases for more examples.

Input will consist of alphabet characters, both uppercase and lowercase. No spaces.

Good luck!

If you like this Kata, please try: 

[Last digit symmetry](https://www.codewars.com/kata/59a9466f589d2af4c50001d8)

[Alternate capitalization](https://www.codewars.com/kata/59cfc000aeb2844d16000075)

~~~if:fortran
## Fortran-Specific Notes

Due to how strings and arrays work in Fortran, some of the strings in the input array will inevitably contain trailing whitespace.  **For this reason, please [trim](https://gcc.gnu.org/onlinedocs/gcc-4.3.4/gfortran/TRIM.html) your input strings before processing them.**
~~~

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
