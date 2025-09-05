**This Kata is intended as a small challenge for my students**

All Star Code Challenge #19

You work for an ad agency and your boss, Bob, loves a catchy slogan. He's always jumbling together "buzz" words until he gets one he likes. You're looking to impress Boss Bob with a function that can do his job for him.

Create a function called sloganMaker() that accepts an array of string "buzz" words. The function returns an array of all possible UNIQUE string permutations of the buzz words (concatonated and separated by spaces).

Your boss is not very bright, so anticipate him using the same "buzz" word more than once, by accident. The function should ignore these duplicate string inputs.

```
sloganMaker(["super", "hot", "guacamole"]);
//[ 'super hot guacamole',
//  'super guacamole hot',
//  'hot super guacamole',
//  'hot guacamole super',
//  'guacamole super hot',
//  'guacamole hot super' ]

sloganMaker(["cool", "pizza", "cool"]); // => [ 'cool pizza', 'pizza cool' ]
```

Note:  
There should be NO duplicate strings in the output array

The input array MAY contain duplicate strings, which should STILL result in an output array with all unique strings

An empty string is valid input

```if-not:python,crystal
The order of the permutations in the output array does not matter
```
```if:python,crystal
The order of the output array must match those rules:
1. Generate the permutations in lexicographic order of the original array.
2. keep only the first occurence of a permutation, when duplicates are found.
```

def List.factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def List.unique {α} [BEq α] (xs : List α) : List α := sorry

def slogan_maker (words: List String) : List String := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded