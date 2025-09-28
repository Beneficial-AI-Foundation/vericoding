// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_triple(a: int, b: int, c: int, n: int, k: int) -> bool
    recommends k >= 1
{
    1 <= a <= n && 1 <= b <= n && 1 <= c <= n &&
    (a + b) % k == 0 && (b + c) % k == 0 && (c + a) % k == 0
}

spec fn count_valid_triples(n: int, k: int) -> int
    recommends n >= 1 && k >= 1
{
    if k % 2 == 1 {
        let cnt1 = n / k;
        cnt1 * cnt1 * cnt1
    } else {
        let cnt1 = n / k;
        let cnt2 = n / k + (if n % k >= k / 2 { 1int } else { 0int });
        cnt1 * cnt1 * cnt1 + cnt2 * cnt2 * cnt2
    }
}

spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 1
}

spec fn count_divisible_by_k(n: int, k: int) -> int
    recommends k >= 1
{
    if n <= 0 { 0int } else { n / k }
}

spec fn count_with_remainder_half_k(n: int, k: int) -> int
    recommends k >= 1
{
    if n <= 0 { 0int } else { n / k + (if n % k >= k / 2 { 1int } else { 0int }) }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_count_nonnegative(n: int, k: int)
    requires
        valid_input(n, k),
    ensures
        count_valid_triples(n, k) >= 0,
{
    if k % 2 == 1 {
        let cnt1 = n / k;
        assert(cnt1 >= 0);
        assert(cnt1 * cnt1 >= 0);
        assert(cnt1 * cnt1 * cnt1 >= 0);
    } else {
        let cnt1 = n / k;
        let cnt2 = n / k + (if n % k >= k / 2 { 1int } else { 0int });
        assert(cnt1 >= 0);
        assert(cnt2 >= 0);
        assert(cnt1 * cnt1 >= 0);
        assert(cnt2 * cnt2 >= 0);
        assert(cnt1 * cnt1 * cnt1 >= 0);
        assert(cnt2 * cnt2 * cnt2 >= 0);
        assert(cnt1 * cnt1 * cnt1 + cnt2 * cnt2 * cnt2 >= 0);
    }
}

proof fn lemma_count_divisible_bounds(n: int, k: int)
    requires
        valid_input(n, k),
    ensures
        0 <= count_divisible_by_k(n, k),
        count_divisible_by_k(n, k) <= n,
{
    let q = if n <= 0 { 0int } else { n / k };
    assert(q == count_divisible_by_k(n, k));
    assert(q >= 0);
    assert(q <= n);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires 
        valid_input(n as int, k as int)
    ensures 
        result >= 0,
        result as int == count_valid_triples(n as int, k as int)
// </vc-spec>
// <vc-code>
{
    let n32: i32 = n as i32;
    let k32: i32 = k as i32;
    let res32: i32;
    if (k32 % 2) != 0 {
        let cnt1: i32 = n32 / k32;
        res32 = cnt1 * cnt1 * cnt1;
    } else {
        let cnt1: i32 = n32 / k32;
        let half_k: i32 = k32 / 2;
        let extra: i32 = if (n32 % k32) >= half_k { 1 } else { 0 };
        let cnt2: i32 = cnt1 + extra;
        res32 = cnt1 * cnt1 * cnt1 + cnt2 * cnt2 * cnt2;
    }
    let result: i8 = res32 as i8;
    result
}
// </vc-code>


}

fn main() {}