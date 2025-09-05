The [Sharkovsky's Theorem](https://en.wikipedia.org/wiki/Sharkovskii%27s_theorem) involves the following ordering of the natural numbers:
```math
3≺5≺7≺9≺ ...\\
≺2·3≺2·5≺2·7≺2·9≺...\\
≺2^n·3≺2^n·5≺2^n·7≺2^n·9≺...\\
≺2^{(n+1)}·3≺2^{(n+1)}·5≺2^{(n+1)}·7≺2^{(n+1)}·9≺...\\
≺2^n≺2^{(n-1)}≺...\\
≺4≺2≺1\\
```

Your task is to complete the function which returns `true` if `$a≺b$` according to this ordering, and `false` otherwise.

You may assume both `$a$` and `$b$` are non-zero positive integers.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded