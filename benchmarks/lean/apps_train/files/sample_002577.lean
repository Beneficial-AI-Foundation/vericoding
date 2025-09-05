Write a program that, given a word, computes the scrabble score for that word.

## Letter Values

You'll need these:

```
Letter                           Value
A, E, I, O, U, L, N, R, S, T       1
D, G                               2
B, C, M, P                         3
F, H, V, W, Y                      4
K                                  5
J, X                               8
Q, Z                               10
```

```if:ruby,javascript,cfml
There will be a preloaded hashtable `$dict` with all these values: `$dict["E"] == 1`. 
```
```if:haskell
There will be a preloaded list of `(Char, Int)` tuples called `dict` with all these values.
```
```if:python
There will be a preloaded dictionary `dict_scores` with all these values: `dict_scores["E"] == 1`
```

## Examples
```
"cabbage" --> 14
```

"cabbage" should be scored as worth 14 points:

- 3 points for C
- 1 point for A, twice
- 3 points for B, twice
- 2 points for G
- 1 point for E

And to total:

`3 + 2*1 + 2*3 + 2 + 1` = `3 + 2 + 6 + 3` = `14`

Empty string should return `0`. The string can contain spaces and letters (upper and lower case), you should calculate the scrabble score only of the letters in that string.

```
""           --> 0
"STREET"    --> 6
"st re et"    --> 6
"ca bba g  e" --> 14
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
