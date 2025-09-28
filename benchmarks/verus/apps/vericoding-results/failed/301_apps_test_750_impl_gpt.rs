// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 1
}

spec fn sheets_needed(n: int) -> (int, int, int) {
    (2 * n, 5 * n, 8 * n)
}

spec fn total_sheets_needed(n: int) -> int {
    2 * n + 5 * n + 8 * n
}

spec fn ceil_div(a: int, b: int) -> int
    recommends b > 0
{
    (a + b - 1) / b
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): prove ceil_div upper bound without nested proof blocks */
proof fn lemma_ceil_upper_bound(a: int, k: int)
    requires
        a >= 0,
        k > 0,
    ensures
        ceil_div(a, k) * k >= a,
{
    let y = a + k - 1;
    let q = y / k;
    let r = y % k;

    assert(0 <= r && r < k) by { };
    assert(y == k * q + r) by { };

    assert(ceil_div(a, k) == (a + k - 1) / k);
    assert(ceil_div(a, k) == q);

    assert(k * q == y - r);
    assert(y - r >= y - (k - 1)) by { assert(r <= k - 1) by { assert(r < k); } };
    assert(y - (k - 1) == a);
    assert(k * q >= a);

    assert(ceil_div(a, k) * k == k * q);
    assert(ceil_div(a, k) * k >= a) by { assert(k * q >= a); };
}

/* helper modified by LLM (iteration 4): minimality of ceil_div without requiring t >= 0 */
proof fn lemma_ceil_minimal(x: int, k: int, t: int)
    requires
        x >= 0,
        k > 0,
        x <= k * t,
    ensures
        ceil_div(x, k) <= t,
{
    let y = x + k - 1;
    let q = y / k;
    let r = y % k;

    assert(0 <= r && r < k) by { };
    assert(y == k * q + r) by { };
    assert(ceil_div(x, k) == (x + k - 1) / k);
    assert(ceil_div(x, k) == q);

    assert(y <= k * t + k - 1) by { assert(x <= k * t); };
    assert(k * t + k - 1 < k * (t + 1));
    assert(y < k * (t + 1));

    assert(ceil_div(x, k) <= t) by {
        if q > t {
            assert(q >= t + 1);
            assert(k * q >= k * (t + 1));
            assert(y >= k * q) by { assert(r >= 0); };
            assert(false) by { assert(y < k * (t + 1)); };
        }
    };
}

/* helper modified by LLM (iteration 4): sum of ceilings lower-bounds ceiling of sum */
proof fn lemma_ceil_sum_lower_bound(a: int, b: int, c: int, k: int)
    requires
        a >= 0,
        b >= 0,
        c >= 0,
        k > 0,
    ensures
        ceil_div(a, k) + ceil_div(b, k) + ceil_div(c, k) >= ceil_div(a + b + c, k),
{
    lemma_ceil_upper_bound(a, k);
    lemma_ceil_upper_bound(b, k);
    lemma_ceil_upper_bound(c, k);

    let s = ceil_div(a, k) + ceil_div(b, k) + ceil_div(c, k);

    assert(k * s >= a + b + c) by {
        assert(k * ceil_div(a, k) >= a);
        assert(k * ceil_div(b, k) >= b);
        assert(k * ceil_div(c, k) >= c);
    };

    lemma_ceil_minimal(a + b + c, k, s);
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires 
        valid_input(n as int, k as int)
    ensures 
        result as int == ceil_div(2 * (n as int), k as int) + ceil_div(5 * (n as int), k as int) + ceil_div(8 * (n as int), k as int),
        result >= 0,
        result as int >= (total_sheets_needed(n as int) + (k as int) - 1) / (k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): compute sum of ceilings using wider i16 arithmetic and cast */
    let n16: i16 = n as i16;
    let k16: i16 = k as i16;

    let c2: i16 = (2i16 * n16 + k16 - 1i16) / k16;
    let c5: i16 = (5i16 * n16 + k16 - 1i16) / k16;
    let c8: i16 = (8i16 * n16 + k16 - 1i16) / k16;

    let s16: i16 = c2 + c5 + c8;
    let result: i8 = s16 as i8;
    result
}
// </vc-code>


}

fn main() {}