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
/* helper modified by LLM (iteration 5): fixed arithmetic lemmas with proper conditions */
proof fn lemma_div_properties(n: int, k: int)
    requires k >= 1
    ensures
        n >= 0 ==> n / k >= 0,
        n >= 0 ==> n / k <= n,
        n == (n / k) * k + (n % k)
{
}

proof fn lemma_mod_properties(n: int, k: int)
    requires k >= 1
    ensures
        0 <= n % k < k,
        n == (n / k) * k + (n % k)
{
}

proof fn lemma_count_bounds(n: int, k: int)
    requires n >= 1 && k >= 1
    ensures
        count_divisible_by_k(n, k) >= 0,
        count_with_remainder_half_k(n, k) >= 0,
        count_divisible_by_k(n, k) <= n,
        count_with_remainder_half_k(n, k) <= n + 1
{
    lemma_div_properties(n, k);
}

proof fn lemma_cube_bounds(cnt: int)
    requires 0 <= cnt <= 127
    ensures cnt * cnt * cnt <= 2_097_152
{
}

proof fn lemma_sum_bounds(cnt1: int, cnt2: int)
    requires
        0 <= cnt1 <= 127,
        0 <= cnt2 <= 127
    ensures cnt1 * cnt1 * cnt1 + cnt2 * cnt2 * cnt2 <= 4_194_304
{
    lemma_cube_bounds(cnt1);
    lemma_cube_bounds(cnt2);
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
    /* code modified by LLM (iteration 5): simplified implementation without overflow assertions */
    if k % 2 == 1 {
        let cnt1 = n / k;
        proof {
            lemma_div_properties(n as int, k as int);
            lemma_count_bounds(n as int, k as int);
            lemma_cube_bounds(cnt1 as int);
        }
        cnt1 * cnt1 * cnt1
    } else {
        let cnt1 = n / k;
        let cnt2 = n / k + (if n % k >= k / 2 { 1i8 } else { 0i8 });
        proof {
            lemma_div_properties(n as int, k as int);
            lemma_mod_properties(n as int, k as int);
            lemma_count_bounds(n as int, k as int);
            lemma_cube_bounds(cnt1 as int);
            lemma_cube_bounds(cnt2 as int);
            lemma_sum_bounds(cnt1 as int, cnt2 as int);
        }
        cnt1 * cnt1 * cnt1 + cnt2 * cnt2 * cnt2
    }
}
// </vc-code>


}

fn main() {}