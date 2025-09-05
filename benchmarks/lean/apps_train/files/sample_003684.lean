The concept of "[smooth number](https://en.wikipedia.org/wiki/Smooth_number)" is applied to all those numbers whose prime factors are lesser than or equal to `7`: `60` is a smooth number (`2 * 2 * 3 * 5`), `111` is not (`3 * 37`).

More specifically, smooth numbers are classified by their highest prime factor and your are tasked with writing a `isSmooth`/`is_smooth` function that returns a string with this classification as it follows:

* 2-smooth numbers should be all defined as a `"power of 2"`, as they are merely that;
* 3-smooth numbers are to return a result of `"3-smooth"`;
* 5-smooth numbers will be labelled as `"Hamming number"`s (incidentally, you might appreciate [this nice kata on them](https://www.codewars.com/kata/hamming-numbers));
* 7-smooth numbers are classified as `"humble numbers"`s;
* for all the other numbers, just return `non-smooth`.

Examples:
```python
is_smooth(16) == "power of 2"
is_smooth(36) == "3-smooth"
is_smooth(60) == "Hamming number"
is_smooth(98) == "humble number"
is_smooth(111) == "non-smooth"
```
The provided input `n` is always going to be a positive number `> 1`.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded