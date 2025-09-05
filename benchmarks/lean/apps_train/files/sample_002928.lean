Following on from [Part 1](http://www.codewars.com/kata/filling-an-array-part-1/), part 2 looks at some more complicated array contents.

So let's try filling an array with...

## ...square numbers
The numbers from `1` to `n*n`

## ...a range of numbers
A range of numbers starting from `start` and increasing by `step`

## ...random numbers
A bunch of random integers between `min` and `max`

## ...prime numbers
All primes starting from `2` (obviously)...

HOTE: All the above functions should take as their first parameter a number that determines the length of the returned array.

def squares : Nat → List Nat
| n => sorry

def num_range : Nat → Int → Int → List Int
| n, start, step => sorry

def rand_range : Nat → Int → Int → List Int
| n, mn, mx => sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
