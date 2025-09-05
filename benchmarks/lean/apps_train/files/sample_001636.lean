Professor Chambouliard hast just discovered a new type of magnet material. He put particles of this material in a box made of small boxes arranged 
in K rows and N columns as a kind of **2D matrix** `K x N` where `K` and `N` are postive integers.
He thinks that his calculations show that the force exerted by the particle in the small box `(k, n)` is:

The total force exerted by the first row with `k = 1` is:

We can go on with `k = 2` and then `k = 3` etc ... and consider:

## Task: 
To help Professor Chambouliard can we calculate the function `doubles` that will take as parameter `maxk` and `maxn` such that `doubles(maxk, maxn) = S(maxk, maxn)`?
Experiences seems to show that this could be something around `0.7` when `maxk` and `maxn` are big enough.

### Examples:
```
doubles(1, 3)  => 0.4236111111111111
doubles(1, 10) => 0.5580321939764581
doubles(10, 100) => 0.6832948559787737
```

### Notes: 
- In `u(1, N)` the dot is the *multiplication operator*.
- Don't truncate or round: 
Have a look in "RUN EXAMPLES" at "assertFuzzyEquals".

- [link to symbol Sigma](https://en.wikipedia.org/wiki/Summation)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible