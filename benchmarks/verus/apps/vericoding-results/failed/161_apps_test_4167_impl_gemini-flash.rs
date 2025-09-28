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
/* helper modified by LLM (iteration 5): No helper is required. */
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
/* code modified by LLM (iteration 5): Fixed type mismatch issues by casting all intermediate calculations to i8 where appropriate. This includes all products and sums. */
{
    let n_int: int = n as int;
    let k_int: int = k as int;

    if k_int % 2 == 1 {
        let count1_i8: i8 = (n_int / k_int) as i8;
        (count1_i8 * count1_i8 * count1_i8) as i8
    } else {
        let count1_i8: i8 = (n_int / k_int) as i8;
        let count2_i8: i8 = (n_int / k_int + (if n_int % k_int >= k_int / 2 { 1int } else { 0int })) as i8;
        ((count1_i8 * count1_i8 * count1_i8) as i8 + (count2_i8 * count2_i8 * count2_i8) as i8) as i8
    }
}
// </vc-code>


}

fn main() {}