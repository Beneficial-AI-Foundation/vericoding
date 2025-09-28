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

proof fn lemma_div_count_valid_triples(n: int, k: int)
    requires
        valid_input(n, k),
    ensures
        count_valid_triples(n, k) == (
            if k % 2 == 1 {
                let cnt1 = n / k;
                cnt1 * cnt1 * cnt1
            } else {
                let cnt1 = n / k;
                let cnt2 = n / k + (if n % k >= k / 2 { 1 } else { 0 });
                cnt1 * cnt1 * cnt1 + cnt2 * cnt2 * cnt2
            }
        )
{
}

proof fn lemma_div_count_relation(n: int, k: int)
    requires
        valid_input(n, k),
    ensures
        count_divisible_by_k(n, k) == n / k,
        count_with_remainder_half_k(n, k) == n / k + (if n % k >= k / 2 { 1 } else { 0 })
{
}

proof fn lemma_even_k_triple_count(n: int, k: int)
    requires
        valid_input(n, k),
        k % 2 == 0,
    ensures
        count_valid_triples(n, k) == (
            let cnt1 = count_divisible_by_k(n, k);
            let cnt2 = count_with_remainder_half_k(n, k);
            cnt1 * cnt1 * cnt1 + cnt2 * cnt2 * cnt2
        )
{
}

proof fn lemma_odd_k_triple_count(n: int, k: int)
    requires
        valid_input(n, k),
        k % 2 == 1,
    ensures
        count_valid_triples(n, k) == (
            let cnt1 = count_divisible_by_k(n, k);
            cnt1 * cnt1 * cnt1
        )
{
}

spec fn count_divisible_by_k_conv(n: i8, k: i8) -> int
    recommends k >= 1
{
    count_divisible_by_k(n as int, k as int)
}

spec fn count_with_remainder_half_k_conv(n: i8, k: i8) -> int
    recommends k >= 1
{
    count_with_remainder_half_k(n as int, k as int)
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
    /* code modified by LLM (iteration 5): Fixed compilation error by removing extra parameter */
    assert(valid_input(n as int, k as int)) by {
        assert(n >= 1 && k >= 1);
    }
    
    let k_int = k as int;
    let n_int = n as int;
    
    if k % 2 == 1 {
        let cnt1_int = count_divisible_by_k(n_int, k_int);
        let cnt1: i8 = cnt1_int as i8;
        cnt1 * cnt1 * cnt1
    } else {
        let cnt1_int = count_divisible_by_k(n_int, k_int);
        let cnt2_int = count_with_remainder_half_k(n_int, k_int);
        let cnt1: i8 = cnt1_int as i8;
        let cnt2: i8 = cnt2_int as i8;
        cnt1 * cnt1 * cnt1 + cnt2 * cnt2 * cnt2
    }
}
// </vc-code>


}

fn main() {}