// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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
        let cnt2 = n / k + (if n % k >= k / 2 { 1 } else { 0 });
        cnt1 * cnt1 * cnt1 + cnt2 * cnt2 * cnt2
    }
}

spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 1
}

spec fn count_divisible_by_k(n: int, k: int) -> int
    recommends k >= 1
{
    if n <= 0 { 0 } else { n / k }
}

spec fn count_with_remainder_half_k(n: int, k: int) -> int
    recommends k >= 1
{
    if n <= 0 { 0 } else { n / k + (if n % k >= k / 2 { 1 } else { 0 }) }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int) -> (result: int)
    requires 
        valid_input(n, k)
    ensures 
        result >= 0,
        result == count_valid_triples(n, k)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}

fn main() {}