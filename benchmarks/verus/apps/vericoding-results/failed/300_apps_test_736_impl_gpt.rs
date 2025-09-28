// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int) -> bool {
    n > 0 && n <= 10000 && m > 1 && m <= 10
}

spec fn min_moves(n: int) -> int
    recommends n > 0
{
    if n % 2 == 0 { n / 2 } else { n / 2 + 1 }
}

spec fn valid_move_count(n: int, k: int) -> bool
    recommends n > 0
{
    min_moves(n) <= k <= n
}

spec fn is_valid_solution(n: int, m: int, result: int) -> bool
    recommends valid_input(n, m)
{
    result == -1 || (result > 0 && result % m == 0 && valid_move_count(n, result))
}

spec fn no_smaller_solution(n: int, m: int, result: int) -> bool
    recommends valid_input(n, m)
{
    result == -1 ==> forall|k: int| min_moves(n) <= k <= n ==> #[trigger] (k % m) != 0
}

spec fn is_minimal_solution(n: int, m: int, result: int) -> bool
    recommends valid_input(n, m)
{
    result != -1 ==> forall|k: int| (min_moves(n) <= k <= n && k < result) ==> #[trigger] (k % m) != 0
}
// </vc-preamble>

// <vc-helpers>
spec fn ceil_mul(l: int, m: int) -> int
    recommends
        m > 0
{
    ((l + m - 1) / m) * m
}

proof fn lemma_ceil_mul_props(l: int, m: int)
    requires
        l >= 0,
        m > 0,
    ensures
        ceil_mul(l, m) >= l,
        ceil_mul(l, m) % m == 0,
        ceil_mul(l, m) < l + m,
        forall|k: int| k % m == 0 && k >= l ==> k >= ceil_mul(l, m),
{
    let a: int = l + m - 1;
    let q: int = a / m;
    let r: int = ceil_mul(l, m);
    assert(r == q * m);
    assert(a == q * m + a % m);
    assert(0 <= a % m && a % m < m);

    // r >= l
    assert(r == a - a % m);
    assert(r >= a - (m - 1));
    assert(a - (m - 1) == l);
    assert(r >= l);

    // r < l + m
    assert(r <= a);
    assert(a < l + m);
    assert(r < l + m);

    // r % m == 0
    assert((q * m) % m == 0);

    // Minimality: any multiple >= l is >= r
    assert(q * m <= a); // from division properties
    assert(q * m - m <= a - m);
    assert((q - 1) * m <= l - 1);

    assert(forall|k: int|
        k % m == 0 && k >= l ==> k >= r
    ) by {
        let k: int;
        assume(k % m == 0 && k >= l);
        let t: int = k / m;
        assert(k == t * m + k % m);
        assert(k % m == 0);
        assert(k == t * m);
        // If t <= q - 1 then k <= (q - 1) * m <= l - 1, contradicting k >= l
        if t <= q - 1 {
            assert(k <= (q - 1) * m);
            assert((q - 1) * m <= l - 1);
            assert(k <= l - 1);
            assert(false);
        }
        assert(t >= q);
        assert(k >= q * m);
        assert(q * m == r);
    }
}

proof fn lemma_no_divisible_in_range_if_ceil_gt_n(l: int, m: int, n: int)
    requires
        l >= 0,
        m > 0,
        n >= l,
        ceil_mul(l, m) > n,
    ensures
        forall|k: int| l <= k <= n ==> k % m != 0,
{
    lemma_ceil_mul_props(l, m);
    let r = ceil_mul(l, m);
    assert(forall|k: int| l <= k <= n ==> k % m != 0) by {
        let k: int;
        assume(l <= k <= n);
        // If k were divisible by m, minimality would give k >= r > n >= k, contradiction
        if k % m == 0 {
            assert(k >= r);
            assert(r > n);
            assert(n >= k);
            assert(false);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: i8)
    requires 
        valid_input(n as int, m as int)
    ensures 
        is_valid_solution(n as int, m as int, result as int) &&
        no_smaller_solution(n as int, m as int, result as int) &&
        is_minimal_solution(n as int, m as int, result as int)
// </vc-spec>
// <vc-code>
{
    let ni: int = n as int;
    let mi: int = m as int;
    let l: int = min_moves(ni);

    // Basic facts from input
    assert(mi > 1);
    assert(mi > 0);
    assert(ni > 0);

    // Compute the smallest multiple of mi that is >= l
    let q: int = (l + mi - 1) / mi;
    let r: int = q * mi;

    proof {
        // Properties of r as the ceiling multiple
        assert(l >= 0);
        lemma_ceil_mul_props(l, mi);
        assert(r >= l);
        assert(r % mi == 0);
        assert(r < l + mi);
    }

    if r <= ni {
        // Cast safety
        assert(l >= 1); // min_moves(ni) >= 1 for ni > 0
        assert(r >= l);
        assert(r >= 1);
        assert(r <= ni);
        assert(ni <= 127);
        assert(-128 <= r && r <= 127);
        let res: i8 = r as i8;

        // The ensures will follow:
        // - res > 0, res % mi == 0, and min_moves(ni) <= res <= ni
        // - minimality: any k in [l, ni) that is < res is not divisible by mi
        res
    } else {
        // No multiple in range; prove the universal property
        assert(ni >= l);
        proof {
            lemma_no_divisible_in_range_if_ceil_gt_n(l, mi, ni);
        }
        let res: i8 = -1i8;
        res
    }
}
// </vc-code>


}

fn main() {}