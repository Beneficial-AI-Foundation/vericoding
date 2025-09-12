// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn comb2(n: int) -> int
    recommends n >= 0
{
    n * (n - 1) / 2
}

spec fn valid_input(n: int, m: int) -> bool
{
    1 <= m <= n
}

spec fn min_friendship_pairs(n: int, m: int) -> int
    recommends valid_input(n, m)
{
    let k = n / m;
    let p = n % m;
    p * comb2(k + 1) + (m - p) * comb2(k)
}

spec fn max_friendship_pairs(n: int, m: int) -> int
    recommends valid_input(n, m)
{
    comb2(n - m + 1)
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int) -> (result: (int, int))
    requires valid_input(n, m)
    ensures ({
        let (min_pairs, max_pairs) = result;
        min_pairs >= 0
    })
    ensures ({
        let (min_pairs, max_pairs) = result;
        max_pairs >= 0
    })
    ensures ({
        let (min_pairs, max_pairs) = result;
        min_pairs <= max_pairs
    })
    ensures ({
        let (min_pairs, max_pairs) = result;
        min_pairs == min_friendship_pairs(n, m)
    })
    ensures ({
        let (min_pairs, max_pairs) = result;
        max_pairs == max_friendship_pairs(n, m)
    })
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    (0, 0)
    // impl-end
}
// </vc-code>


}

fn main() {}