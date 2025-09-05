A *Vampire number* is a positive integer `z` with a factorization `x * y = z` such that

- `x` and `y` have the same number of digits and
- the multiset of digits of `z` is equal to the multiset of digits of `x` and `y`.
- Additionally, to avoid trivialities, `x` and `y` may not both end with `0`.

In this case, `x` and `y` are called *fangs* of `z`. (The fangs of a Vampire number may not be unique, but this shouldn't bother us.) The first three Vampire numbers are

```
1260 = 21*60
1395 = 15*93
1435 = 35*41
```

Write an algorithm that on input `k` returns the `k`th Vampire number. To avoid time-outs, the Python version will test with `1 <= k <= 155`.

PS: In the OEIS, the Vampire numbers are sequence [A014575](https://oeis.org/A014575).

PPS: So called *Pseudo-Vampire Numbers* are treated in [this kata](http://www.codewars.com/kata/vampire-numbers-1).

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
